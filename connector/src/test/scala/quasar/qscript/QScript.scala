/*
 * Copyright 2014–2017 SlamData Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package quasar.qscript

import slamdata.Predef.{Eq => _, _}
import quasar.{Data, TreeMatchers, Type}
import quasar.common.{JoinType, SortDir}
import quasar.contrib.pathy.{ADir, AFile}
import quasar.fp._
import quasar.fp.ski._
import quasar.frontend.{logicalplan => lp}
import quasar.qscript.MapFuncsCore._
import quasar.sql.{CompilerHelpers, JoinDir, SqlStringContext}
import quasar.std.StdLib
import StdLib._

import scala.collection.immutable.{Map => ScalaMap}
import matryoshka._
import matryoshka.data.Fix
import matryoshka.implicits._
import pathy.Path._
import quasar.ejson.EJson

import scalaz._
import scalaz.syntax.std.option._
import scalaz.syntax.either._
import scalaz.syntax.nel._

class QScriptSpec
    extends quasar.Qspec
    with CompilerHelpers
    with QScriptHelpers
    with TreeMatchers {
  // TODO instead of calling `.toOption` on the `\/`
  // write an `Equal[PlannerError]` and test for specific errors too
  "replan" should {
    "convert a constant boolean" in {
       // "select true"
       convert(lc.some, lpf.constant(Data.Bool(true))) must
         beSome(beTreeEqual(
           fix.Map(fix.Unreferenced, BoolLit(true))))
    }

    "fail to convert a constant set" in {
      // "select {\"a\": 1, \"b\": 2, \"c\": 3, \"d\": 4, \"e\": 5}{*} limit 3 offset 1"
      convert(
        lc.some,
        lpf.constant(Data.Set(List(
          Data.Obj(ListMap("0" -> Data.Int(2))),
          Data.Obj(ListMap("0" -> Data.Int(3))))))) must beNone
    }

    "convert a simple read" in {
      convert(lc.some, lpRead("/foo/bar")) must
      beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> dir("foo") </> file("bar")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide)))
      )
    }

    // FIXME: This can be simplified to a Union of the Reads - the LeftShift
    //        cancels out the MakeMaps.
    "convert a directory read" in {
      convert(lc.some, lpRead("/foo")) must
      beSome(beTreeEqual(chainR(
        fix.Read[ADir](rootDir </> dir("foo")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide))))
    }

    "convert a squashed read" in {
      // "select * from foo"
      convert(lc.some, identity.Squash(lpRead("/foo/bar")).embed) must
      beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> dir("foo") </> file("bar")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide))))
    }

    "convert a basic select with type checking" in {
      val lp = fullCompileExp(sqlE"select foo as foo from bar")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("bar")))(
        fix.LeftShift(_,
          func.Hole,
          ExcludeId,
          func.MakeMap(
            func.StrLit("foo"),
            func.Guard(
              func.RightSide,
              Type.Obj(ScalaMap(), Some(Type.Top)),
              func.ProjectKey(func.RightSide, func.StrLit("foo")),
              func.Undefined))))))
    }

    // TODO: This would benefit from better normalization around Sort (#1545)
    "convert a basic order by" in {
      val lp = fullCompileExp(sqlE"select * from zips order by city")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
          func.ConcatArrays(
            func.MakeArray(
              func.Guard(
                func.ProjectIndex(func.RightSide, func.IntLit(1)),
                Type.Obj(scala.Predef.Map(), Type.Top.some),
                func.ProjectIndex(func.RightSide, func.IntLit(1)),
                func.Undefined)),
            func.MakeArray(
              func.Guard(
                func.ProjectIndex(func.RightSide, func.IntLit(1)),
                Type.Obj(scala.Predef.Map(), Type.Top.some),
                func.ProjectKey(
                  func.ProjectIndex(func.RightSide, func.IntLit(1)),
                  func.StrLit("city")),
                func.Undefined)))),
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole, func.IntLit(1)), SortDir.asc).wrapNel),
        fix.Map(_, func.ProjectIndex(func.Hole, func.IntLit(0))))))
    }

    "convert a basic reduction" in {
      val lp = fullCompileExp(sqlE"select sum(pop) as pop from bar")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("bar")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide),
        fix.Reduce(_,
          Nil,
          List(ReduceFuncs.Sum(
            func.Guard(
              func.Hole, Type.Obj(ScalaMap(), Type.Top.some),
              func.Guard(
                func.ProjectKey(func.Hole, func.StrLit("pop")),
                Type.Coproduct(Type.Coproduct(Type.Int, Type.Dec), Type.Interval),
                func.ProjectKey(func.Hole, func.StrLit("pop")),
                func.Undefined),
              func.Undefined))),
          func.MakeMap(func.StrLit("pop"), func.ReduceIndex(0.right))))))
    }

    "convert a simple wildcard take" in {
      val lp = fullCompileExp(sqlE"select * from bar limit 10")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(
        fix.Subset(fix.Unreferenced,
          free.LeftShift(free.Read[AFile](rootDir </> file("bar")), func.Hole, ExcludeId, func.RightSide),
          Take,
          free.Map(free.Unreferenced, func.IntLit(10)))))
    }

    "convert a simple take through a path" in {
      convert(lc.some, StdLib.set.Take(lpRead("/foo/bar"), lpf.constant(Data.Int(10))).embed) must
        beSome(beTreeEqual(
          fix.Subset(
            fix.Unreferenced,
            free.LeftShift(free.Read[AFile](rootDir </> dir("foo") </> file("bar")), func.Hole, ExcludeId, func.RightSide),
            Take,
            free.Map(free.Unreferenced, func.IntLit(10)))))
    }

    "convert a multi-field select" in {
      val lp = fullCompileExp(sqlE"select city, state from bar")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("bar")))(
        fix.LeftShift(_,
          func.Hole,
          ExcludeId,
          func.ConcatMaps(
            func.MakeMap(
              func.StrLit("city"),
              func.Guard(
                func.RightSide,
                Type.Obj(ScalaMap(), Some(Type.Top)),
                func.ProjectKey(func.RightSide, func.StrLit("city")),
                func.Undefined)),
            func.MakeMap(
              func.StrLit("state"),
              func.Guard(
                func.RightSide,
                Type.Obj(ScalaMap(), Some(Type.Top)),
                func.ProjectKey(func.RightSide, func.StrLit("state")),
                func.Undefined)))))))
    }

    "convert a simple read with path projects" in {
      convert(lc.some, lpRead("/some/bar/car")) must
        beSome(beTreeEqual(chainR(
          fix.Read[AFile](rootDir </> dir("some") </> file("bar")))(
          fix.LeftShift(_,
            func.ProjectKey(func.Hole, func.StrLit("car")),
            ExcludeId,
            func.RightSide))))
    }

    "convert a basic invoke" in {
      convert(None, math.Add(lpRead("/foo"), lpRead("/bar")).embed) must
        beSome(beTreeEqual(chainR(
          fix.Root)(
          fix.ThetaJoin(_,
            free.LeftShift(
              free.Map(
                free.Hole,
                func.ProjectKey(func.Hole, func.StrLit("foo"))),
              func.Hole,
              IncludeId,
              func.RightSide),
            free.LeftShift(
              free.Map(
                free.Hole,
                func.ProjectKey(func.Hole, func.StrLit("bar"))),
              func.Hole,
              IncludeId,
              func.RightSide),
            func.BoolLit(true),
            JoinType.Inner,
            func.Add(
              func.ProjectIndex(func.LeftSide, func.IntLit(1)),
              func.ProjectIndex(func.RightSide, func.IntLit(1)))))))
    }

    "convert project object and make object" in {
      convert(
        None,
        identity.Squash(
          makeObj(
            "name" -> structural.MapProject(
              lpRead("/city"),
              lpf.constant(Data.Str("name"))).embed)).embed) must
      beSome(beTreeEqual(chainR(
        fix.Root)(
        fix.LeftShift(_,
          ProjectKeyR(func.Hole, StrLit("city")),
          ExcludeId,
          func.MakeMap(
            func.StrLit("name"),
            func.ProjectKey(func.RightSide, func.StrLit("name")))))))
    }

    "convert a basic reduction" in {
      convert(
        lc.some,
        agg.Sum(lpRead("/person")).embed) must
        beSome(beTreeEqual(chainR(
          fix.Read[AFile](rootDir </> file("person")))(
          fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide),
          fix.Reduce(_,
            Nil,
            List(ReduceFuncs.Sum(func.Hole)),
            func.ReduceIndex(0.right)))))
    }

    "convert a basic reduction wrapped in an object" in {
      // "select sum(height) from person"
      convert(
        None,
        makeObj(
          "0" ->
            agg.Sum(structural.MapProject(lpRead("/person"), lpf.constant(Data.Str("height"))).embed).embed)) must
      beSome(beTreeEqual(chainR(
        fix.Root)(
        fix.LeftShift(_,
          ProjectKeyR(func.Hole, StrLit("person")),
          ExcludeId,
          func.RightSide),
        fix.Reduce(_,
          Nil,
          List(ReduceFuncs.Sum[FreeMap](ProjectKeyR(func.Hole, StrLit("height")))),
          func.MakeMap(StrLit("0"), Free.point(ReduceIndex(0.right)))))))
    }

    "convert a flatten array" in {
      // "select loc[:*] from zips",
      convert(
        None,
        makeObj(
          "loc" ->
            structural.FlattenArray(
              structural.MapProject(lpRead("/zips"), lpf.constant(Data.Str("loc"))).embed).embed)) must
      beSome(beTreeEqual(chainR(
        fix.Root)(
        fix.LeftShift(_,
          func.ProjectKey(func.Hole, func.StrLit("zips")),
          ExcludeId,
          func.ProjectKey(func.RightSide, func.StrLit("loc"))),
        fix.LeftShift(_,
          func.Hole,
          ExcludeId,
          func.MakeMap(StrLit("loc"), func.RightSide)))))
    }

    "convert a constant shift array of size one" in {
      // this query never makes it to LP->QS transform because it's a constant value
      // "foo := (7); select * from foo"
      convert(
        None,
        identity.Squash(
          structural.ShiftArray(
            structural.MakeArrayN(lpf.constant(Data.Int(7))).embed).embed).embed) must
        beSome(beTreeEqual(chainR(
          fix.Unreferenced)(
          fix.LeftShift(_,
            func.Constant(EJson.arr[Fix](EJson.int[Fix](7))),
            ExcludeId,
            func.RightSide))))
    }

    "convert a constant shift array of size two" in {
      // this query never makes it to LP->QS transform because it's a constant value
      // "foo := (7,8); select * from foo"
      convert(
        None,
        identity.Squash(
          structural.ShiftArray(
            structural.ArrayConcat(
              structural.MakeArrayN(lpf.constant(Data.Int(7))).embed,
              structural.MakeArrayN(lpf.constant(Data.Int(8))).embed).embed).embed).embed) must
        beSome(beTreeEqual(chainR(
          fix.Unreferenced)(
          fix.LeftShift(
            _,
            func.Constant(EJson.arr[Fix](EJson.int[Fix](7), EJson.int[Fix](8))),
            ExcludeId,
            func.RightSide))))
    }

    "convert a constant shift array of size three" in {
      // this query never makes it to LP->QS transform because it's a constant value
      // "foo := (7,8,9); select * from foo"
      convert(
        None,
        identity.Squash(
          structural.ShiftArray(
            structural.ArrayConcat(
              structural.ArrayConcat(
                structural.MakeArrayN(lpf.constant(Data.Int(7))).embed,
                structural.MakeArrayN(lpf.constant(Data.Int(8))).embed).embed,
              structural.MakeArrayN(lpf.constant(Data.Int(9))).embed).embed).embed).embed) must
        beSome(beTreeEqual(chainR(
          fix.Unreferenced)(
          fix.LeftShift(_,
            func.Constant(EJson.arr[Fix](EJson.int[Fix](7), EJson.int[Fix](8), EJson.int[Fix](9))),
            ExcludeId,
            func.RightSide))))
    }

    "convert a read shift array" in {
      // select (baz || quux || ducks)[*] from `/foo/bar`
      convert(
        None,
        lp.let('x, lpRead("/foo/bar"),
          structural.ShiftArray(
            structural.ArrayConcat(
              structural.ArrayConcat(
                structural.MapProject(lpf.free('x), lpf.constant(Data.Str("baz"))).embed,
                structural.MapProject(lpf.free('x), lpf.constant(Data.Str("quux"))).embed).embed,
              structural.MapProject(lpf.free('x), lpf.constant(Data.Str("ducks"))).embed).embed).embed).embed) must
        beSome(beTreeEqual(chainR(
          fix.Root)(
          fix.LeftShift(_,
            func.ProjectKey(func.ProjectKey(func.Hole, func.StrLit("foo")), func.StrLit("bar")),
            ExcludeId,
            func.ConcatArrays(
              func.ConcatArrays(
                func.ProjectKey(func.RightSide, func.StrLit("baz")),
                func.ProjectKey(func.RightSide, func.StrLit("quux"))),
              func.ProjectKey(func.RightSide, func.StrLit("ducks")))),
          fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide))))
    }

    "convert a shift/unshift array" in {
      // "select [loc[_:] * 10 ...] from zips",
      convert(
        lc.some,
        makeObj(
          "0" ->
            structural.UnshiftArray(
              math.Multiply(
                structural.ShiftArrayIndices(
                  structural.MapProject(lpRead("/zips"), lpf.constant(Data.Str("loc"))).embed).embed,
                lpf.constant(Data.Int(10))).embed).embed)) must
      beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
          func.ConcatArrays(
            func.MakeArray(func.LeftSide),
            func.MakeArray(func.RightSide))),
        fix.LeftShift(_,
          func.ProjectKey(
            func.ProjectIndex(func.ProjectIndex(func.Hole, func.IntLit(1)), func.IntLit(1)),
            func.StrLit("loc")),
          IdOnly,
          func.ConcatArrays(
            func.MakeArray(func.LeftSide),
            func.MakeArray(func.RightSide))),
        fix.Reduce(_,
          List(
            func.ProjectIndex(
              func.ProjectIndex(func.ProjectIndex(func.Hole,func.IntLit(0)),func.IntLit(1)),
              func.IntLit(0))),
          List(
            ReduceFuncs.UnshiftArray(
              func.Multiply(
                func.ProjectIndex(func.Hole, func.IntLit(1)),
                func.IntLit(10)))),
          func.MakeMap(
            func.StrLit("0"),
            func.ReduceIndex(0.right))))))
    }

    "convert a filter" in {
      // "select * from foo where baz between 1 and 10"
      convert(
        lc.some,
        StdLib.set.Filter(
          lpRead("/bar"),
          relations.Between(
            structural.MapProject(lpRead("/bar"), lpf.constant(Data.Str("baz"))).embed,
            lpf.constant(Data.Int(1)),
            lpf.constant(Data.Int(10))).embed).embed) must
        beSome(beTreeEqual(chainR(
          fix.Read[AFile](rootDir </> file("bar")))(
          fix.LeftShift(_,
            func.Hole,
            IncludeId,
            func.ConcatArrays(
              func.MakeArray(func.ProjectIndex(func.RightSide, func.IntLit(1))),
              func.MakeArray(
                func.Between(
                  func.ProjectKey(
                    func.ProjectIndex(func.RightSide, func.IntLit(1)),
                    func.StrLit("baz")),
                  func.IntLit(1),
                  func.IntLit(10))))),
          fix.Filter(_, func.ProjectIndex(func.Hole, func.IntLit(1))),
          fix.Map(_, func.ProjectIndex(func.Hole, func.IntLit(0))))))
    }

    // an example of how logical plan expects magical "left" and "right" keys to exist
    "convert magical query" in {
      // "select * from person, car",
      convert(
        lc.some,
        lp.let('__tmp0,
          lp.join(
            lpRead("/person"),
            lpRead("/car"),
            JoinType.Inner,
            lp.JoinCondition('__leftJoin5, '__rightJoin6, lpf.constant(Data.Bool(true)))).embed,
          identity.Squash(
            structural.MapConcat(
              JoinDir.Left.projectFrom(lpf.free('__tmp0)),
              JoinDir.Right.projectFrom(lpf.free('__tmp0))).embed).embed).embed) must
      beSome(beTreeEqual(chainR(
        fix.Unreferenced)(
        fix.ThetaJoin(_,
          free.LeftShift(
            free.Read[AFile](rootDir </> file("person")),
            func.Hole,
            IncludeId,
            func.RightSide),
          free.LeftShift(
            free.Read[AFile](rootDir </> file("car")),
            func.Hole,
            IncludeId,
            func.RightSide),
          func.BoolLit(true),
          JoinType.Inner,
          func.ConcatMaps(
            func.ProjectIndex(func.LeftSide, func.IntLit(1)),
            func.ProjectIndex(func.RightSide, func.IntLit(1)))))))
    }

    "convert basic join with explicit join condition" in {
      //"select foo.name, bar.address from foo join bar on foo.id = bar.foo_id",

      val query =
        lpf.let('__tmp0,
          lpf.join(
            lpRead("/foo"),
            lpRead("/bar"),
            JoinType.Inner,
            lp.JoinCondition('__leftJoin9, '__rightJoin10,
              relations.Eq(
                structural.MapProject(lpf.joinSideName('__leftJoin9), lpf.constant(Data.Str("id"))).embed,
                structural.MapProject(lpf.joinSideName('__rightJoin10), lpf.constant(Data.Str("foo_id"))).embed).embed)),
          makeObj(
            "name" ->
              structural.MapProject(
                JoinDir.Left.projectFrom(lpf.free('__tmp0)),
                lpf.constant(Data.Str("name"))).embed,
            "address" ->
              structural.MapProject(
                JoinDir.Right.projectFrom(lpf.free('__tmp0)),
                lpf.constant(Data.Str("address"))).embed))

      convert(None, query) must
        beSome(beTreeEqual(chainR(
          fix.Root)(
          fix.ThetaJoin(_,
            free.LeftShift(
              free.Map(free.Hole, func.ProjectKey(func.Hole, func.StrLit("foo"))),
          func.Hole,
              IncludeId,
          func.RightSide),
            free.LeftShift(
              free.Map(free.Hole, func.ProjectKey(func.Hole, func.StrLit("bar"))),
              func.Hole,
              IncludeId,
              func.RightSide),
            func.Eq(
              func.ProjectKey(
                func.ProjectIndex(func.LeftSide, IntLit(1)),
                func.StrLit("id")),
              func.ProjectKey(
                func.ProjectIndex(func.RightSide, IntLit(1)),
                func.StrLit("foo_id"))),
            JoinType.Inner,
            func.ConcatMaps(
              func.MakeMap(
                func.StrLit("name"),
                func.ProjectKey(
                  func.ProjectIndex(func.LeftSide, func.IntLit(1)),
                  func.StrLit("name"))),
              func.MakeMap(
                func.StrLit("address"),
                func.ProjectKey(
                  func.ProjectIndex(func.RightSide, func.IntLit(1)),
                  func.StrLit("address"))))))))
    }

    "convert union" in {
      val lp = fullCompileExp(sqlE"select * from city union select * from person")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Unreferenced)(
        fix.Union(_,
          free.LeftShift(
            free.Read[AFile](rootDir </> file("city")),
            func.Hole,
            ExcludeId,
            func.ConcatArrays(
              func.MakeArray(
                func.ProjectIndex(func.ProjectIndex(func.RightSide, func.IntLit(1)), func.IntLit(0))),
              func.MakeArray(func.RightSide))),
          free.LeftShift(
            free.Read[AFile](rootDir </> file("person")),
            func.Hole,
            ExcludeId,
            func.ConcatArrays(
              func.MakeArray(
                func.ProjectIndex(func.ProjectIndex(func.RightSide, func.IntLit(1)), func.IntLit(0))),
              func.MakeArray(func.RightSide)))),
        fix.Reduce(_,
          List(func.ProjectIndex(func.Hole,func.IntLit(1))),
          // FIXME: This should be fetched from the bucket
          List(ReduceFuncs.Arbitrary(func.ProjectIndex(func.Hole, func.IntLit(1)))),
          func.ReduceIndex(0.right)))))
    }

    "convert distinct by" in {
      val lp = fullCompileExp(sqlE"select distinct(city) from zips order by pop")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
          func.ConcatArrays(
            func.MakeArray(
              func.ConcatMaps(
                func.MakeMap(
                 func.StrLit("city"),
                  func.Guard(
                    func.ProjectIndex(func.RightSide,func.IntLit(1)),
                    Type.Obj(ScalaMap(), Some(Type.Top)),
                    func.ProjectKey(
                      func.ProjectIndex(func.RightSide,func.IntLit(1)),
                     func.StrLit("city")),
                    func.Undefined)),
                func.MakeMap(
                 func.StrLit("__sd__0"),
                  func.Guard(
                    func.ProjectIndex(func.RightSide,func.IntLit(1)),
                    Type.Obj(ScalaMap(), Some(Type.Top)),
                    func.ProjectKey(
                      func.ProjectIndex(func.RightSide,func.IntLit(1)),
                     func.StrLit("pop")),
                    func.Undefined)))),
            func.MakeArray(
              func.Guard(
                func.ProjectIndex(func.RightSide,func.IntLit(1)),
                Type.Obj(ScalaMap(), Some(Type.Top)),
                func.ProjectKey(
                  func.ProjectIndex(func.RightSide,func.IntLit(1)),
                 func.StrLit("pop")),
                func.Undefined)))),
        // FIXME #2034
        // this `Sort` should sort by the representation of the synthetic key "__sd0__"
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole, func.IntLit(1)) -> SortDir.asc).wrapNel),
        fix.Reduce(_,
          List(func.DeleteKey(func.ProjectIndex(func.Hole,func.IntLit(0)),func.StrLit("__sd__0"))),
          List(ReduceFuncs.First(func.ProjectIndex(func.Hole,func.IntLit(0)))),
          func.ConcatArrays(
            func.ConcatArrays(
              func.MakeArray(func.ReduceIndex(0.left)),
              func.MakeArray(func.ReduceIndex(0.right))),
            func.MakeArray(
              func.ProjectKey(func.ReduceIndex(0.right),func.StrLit("__sd__0"))))),
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole,func.IntLit(2)) -> SortDir.asc).wrapNel),
        fix.Map(_,
          func.DeleteKey(func.ProjectIndex(func.Hole,func.IntLit(1)),func.StrLit("__sd__0"))))))
    }

    "convert a multi-key reduce" in {
      val lp = fullCompileExp(sqlE"select max(pop), min(city) from zips")
      val qs = convert(lc.some, lp)
      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide),
        fix.Reduce(_,
          Nil,
          List(
            ReduceFuncs.Max(
              func.Guard(
                func.Guard(
                  func.Hole,
                  Type.Obj(ScalaMap(), Some(Type.Top)),
                  func.ProjectKey(func.Hole, func.StrLit("pop")),
                  func.Undefined),
                Type.Coproduct(Type.Int, Type.Coproduct(Type.Dec, Type.Coproduct(Type.Interval, Type.Coproduct(Type.Str, Type.Coproduct(Type.Timestamp, Type.Coproduct(Type.Date, Type.Coproduct(Type.Time, Type.Bool))))))),
                func.Guard(
                  func.Hole,
                  Type.Obj(ScalaMap(), Some(Type.Top)),
                  func.ProjectKey(func.Hole, func.StrLit("pop")),
                  func.Undefined),
                func.Undefined)),
            ReduceFuncs.Min(
              func.Guard(
                func.Guard(
                  func.Hole,
                  Type.Obj(ScalaMap(), Some(Type.Top)),
                  func.ProjectKey(func.Hole, func.StrLit("city")),
                  func.Undefined),
                Type.Coproduct(Type.Int, Type.Coproduct(Type.Dec, Type.Coproduct(Type.Interval, Type.Coproduct(Type.Str, Type.Coproduct(Type.Timestamp, Type.Coproduct(Type.Date, Type.Coproduct(Type.Time, Type.Bool))))))),
                func.Guard(
                  func.Hole,
                  Type.Obj(ScalaMap(), Some(Type.Top)),
                  func.ProjectKey(func.Hole, func.StrLit("city")),
                  func.Undefined),
                func.Undefined))),
          func.ConcatMaps(
            func.MakeMap(StrLit("0"), func.ReduceIndex(0.right)),
            func.MakeMap(StrLit("1"), func.ReduceIndex(1.right)))))))
    }

    "convert a filter followed by a reduce" in {
      val lp = fullCompileExp(sqlE"select count(*) from zips where pop > 1000")
      val qs = convert(lc.some, lp)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
           func.ConcatArrays(
             func.MakeArray(
               func.Guard(
                 func.ProjectIndex(func.RightSide, func.IntLit(1)),
                 Type.Obj(ScalaMap(), Some(Type.Top)),
                 func.ProjectIndex(func.RightSide, func.IntLit(1)),
                 func.Undefined)),
             func.MakeArray(
               func.Guard(
                 func.Guard(
                   func.ProjectIndex(func.RightSide, func.IntLit(1)),
                   Type.Obj(ScalaMap(), Some(Type.Top)),
                   func.ProjectKey(
                     func.ProjectIndex(func.RightSide, func.IntLit(1)),
                    func.StrLit("pop")),
                   func.Undefined),
                 Type.Coproduct(Type.Int, Type.Coproduct(Type.Dec, Type.Coproduct(Type.Interval, Type.Coproduct(Type.Str, Type.Coproduct(Type.Timestamp, Type.Coproduct(Type.Date, Type.Coproduct(Type.Time, Type.Bool))))))),
                 func.Guard(
                   func.ProjectIndex(func.RightSide, func.IntLit(1)),
                   Type.Obj(ScalaMap(), Some(Type.Top)),
                   func.Gt(
                     func.ProjectKey(
                       func.ProjectIndex(func.RightSide, func.IntLit(1)),
                      func.StrLit("pop")),
                    func.IntLit(1000)),
                   func.Undefined),
                 func.Undefined)))),
        fix.Filter(_,
          func.ProjectIndex(func.Hole, func.IntLit(1))),
        fix.Reduce(_,
          Nil,
          List(ReduceFuncs.Count[FreeMap](func.ProjectIndex(func.Hole, func.IntLit(0)))),
          func.ReduceIndex(0.right)))))
    }

    "convert a sort of a single value unary reduction" in {
      val lp = fullCompileExp(sqlE"select count(*) as cnt from zips order by cnt")
      val qs = convert(lc.some, lp)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide),
        fix.Reduce(_,
          Nil,
          List(ReduceFuncs.Count[FreeMap](func.Hole)),
          func.ConcatArrays(
            func.MakeArray(func.MakeMap(StrLit("cnt"), func.ReduceIndex(0.right))),
            func.MakeArray(func.ReduceIndex(0.right)))),
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole, func.IntLit(1)), SortDir.asc).wrapNel),
        fix.Map(_, func.ProjectIndex(func.Hole, func.IntLit(0))))))
    }

    "convert a sort of a single value binary reduction" in {
      val lp = fullCompileExp(sqlE"select {y : z ...} as x from zips order by x")
      val qs = convert(lc.some, lp)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_, func.Hole, IncludeId, func.RightSide),
        fix.Reduce(_,
          Nil,
          List(ReduceFuncs.UnshiftMap[FreeMap](
            func.ProjectIndex(func.Hole, func.IntLit(1)),
            func.ProjectIndex(
              func.ConcatArrays(
                func.MakeArray(func.ProjectIndex(func.Hole, func.IntLit(0))),
                func.MakeArray(func.ProjectIndex(func.Hole, func.IntLit(1)))),
             func.IntLit(2)))),
          func.ConcatArrays(
            func.MakeArray(func.MakeMap(StrLit("x"), func.ReduceIndex(0.right))),
            func.MakeArray(func.ReduceIndex(0.right)))),
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole, func.IntLit(1)), SortDir.asc).wrapNel),
        fix.Map(_, func.ProjectIndex(func.Hole, func.IntLit(0))))))
    }

    "convert a non-static array projection" in {
      val lp = fullCompileExp(sqlE"select (loc || [7, 8])[0] from zips")
      val qs = convert(lc.some, lp)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          ExcludeId,
          func.Guard(
            func.RightSide,
            Type.Obj(ScalaMap(), Some(Type.Top)),
            func.Guard(
              func.ProjectKey(func.RightSide, func.StrLit("loc")),
              Type.FlexArr(0, None, Type.Top),
              func.ProjectIndex(
                func.ConcatArrays(
                  func.ProjectKey(func.RightSide, func.StrLit("loc")),
                  func.Constant(EJson.arr[Fix](EJson.int[Fix](7), EJson.int[Fix](8)))),
               func.IntLit(0)),
              func.Undefined),
            func.Undefined)))))
    }

    "convert a static array projection prefix" in {
      val lp = fullCompileExp(sqlE"select ([7, 8] || loc)[1] from zips")
      val qs = convert(lc.some, lp)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          ExcludeId,
          func.Guard(
            func.RightSide,
            Type.Obj(ScalaMap(), Some(Type.Top)),
            func.Guard(
              func.ProjectKey(func.RightSide, func.StrLit("loc")),
              Type.FlexArr(0, None, Type.Top),
             func.IntLit(8),
              func.Undefined),
            func.Undefined)))))
    }

    "convert a group by with reduction" in {
      val lp = fullCompileExp(sqlE"select (loc[0] > -78.0) as l, count(*) as c from zips group by (loc[0] > -78.0)")
      val qs = convert(lc.some, lp)

      val inner: FreeMap =
        func.Guard(
          func.Guard(
            func.Hole,
            Type.Obj(ScalaMap(), Some(Type.Top)),
            func.ProjectKey(func.Hole, func.StrLit("loc")),
            func.Undefined),
          Type.FlexArr(0, None, Type.Top),
          func.Guard(
            func.Guard(
              func.Hole,
              Type.Obj(ScalaMap(), Some(Type.Top)),
              func.ProjectIndex(func.ProjectKey(func.Hole, func.StrLit("loc")), func.IntLit(0)),
              func.Undefined),
            Type.Coproduct(Type.Int, Type.Coproduct(Type.Dec, Type.Coproduct(Type.Interval, Type.Coproduct(Type.Str, Type.Coproduct(Type.Timestamp, Type.Coproduct(Type.Date, Type.Coproduct(Type.Time, Type.Bool))))))),
            func.Guard(
              func.Hole,
              Type.Obj(ScalaMap(), Some(Type.Top)),
              func.Gt(
                func.ProjectIndex(func.ProjectKey(func.Hole, func.StrLit("loc")), func.IntLit(0)),
                DecLit(-78.0)),
              func.Undefined),
            func.Undefined),
          func.Undefined)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_, func.Hole, ExcludeId, func.RightSide),
        fix.Reduce(_,
          List(func.MakeArray(inner)),
          List(
            ReduceFuncs.Arbitrary(inner),
            ReduceFuncs.Count(func.Guard(
              func.Hole,
              Type.Obj(ScalaMap(), Some(Type.Top)),
              func.Hole,
              func.Undefined))),
          func.ConcatMaps(
            func.MakeMap(StrLit("l"), func.ReduceIndex(0.right)),
            func.MakeMap(StrLit("c"), func.ReduceIndex(1.right)))))))

    }

    "convert an ordered filtered distinct" in {
      val lp = fullCompileExp(sqlE"select distinct city from zips where pop <= 10 order by pop")
      val qs = convert(lc.some, lp)

      def guard(jf: JoinFunc => JoinFunc): JoinFunc =
        func.Guard(
          func.ProjectIndex(func.RightSide, func.IntLit(1)),
          Type.Obj(ScalaMap(), Some(Type.Top)),
          jf(func.ProjectIndex(func.RightSide, func.IntLit(1))),
          func.Undefined)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
          func.ConcatArrays(
            func.MakeArray(guard(ι)),
            func.MakeArray(func.Guard(
              guard(func.ProjectKey(_, func.StrLit("pop"))),
              Type.Coproduct(Type.Int, Type.Coproduct(Type.Dec, Type.Coproduct(Type.Interval, Type.Coproduct(Type.Str, Type.Coproduct(Type.Timestamp, Type.Coproduct(Type.Date, Type.Coproduct(Type.Time, Type.Bool))))))),
              guard(jf => func.Lte(func.ProjectKey(jf, func.StrLit("pop")), func.IntLit(10))),
              func.Undefined)))),
        fix.Filter(_,
          func.ProjectIndex(func.Hole, func.IntLit(1))),
        // FIXME #2034
        // this `Sort` should sort by the representation of the synthetic key "__sd0__"
        fix.Sort(_,
          Nil,
          (func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("pop")), SortDir.asc).wrapNel),
        fix.Reduce(_,
          List(
            func.MakeMap(
             func.StrLit("city"),
              func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("city")))),
          List(
            ReduceFuncs.First(func.ConcatMaps(
              func.MakeMap(StrLit("city"), func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("city"))),
              func.MakeMap(StrLit("__sd__0"), func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("pop")))))),
          func.ConcatArrays(
            func.ConcatArrays(
              func.MakeArray(func.ReduceIndex(0.left)),
              func.MakeArray(func.ReduceIndex(0.right))),
            func.MakeArray(func.ProjectKey(func.ReduceIndex(0.right), func.StrLit("__sd__0"))))),
        // FIXME #2034
        // this `Sort` should sort by the representation of the synthetic key "__sd0__"
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole, func.IntLit(2)), SortDir.asc).wrapNel),
        fix.Map(_, func.DeleteKey(func.ProjectIndex(func.Hole, func.IntLit(1)), func.StrLit("__sd__0"))))))
    }

    "convert an ordered filtered distinct with cases" in {
      val lp = fullCompileExp(sqlE"""select distinct case state when "MA" then "Massachusetts" else "unknown" end as name from zips where pop <= 10 order by pop""")
      val qs = convert(lc.some, lp)

      def guard(jf: JoinFunc => JoinFunc): JoinFunc =
        func.Guard(
          func.ProjectIndex(func.RightSide, func.IntLit(1)),
          Type.Obj(ScalaMap(), Some(Type.Top)),
          jf(func.ProjectIndex(func.RightSide, func.IntLit(1))),
          func.Undefined)

      val cond: FreeMap =
        func.Cond(
          func.Eq(func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("state")), func.StrLit("MA")),
          func.StrLit("Massachusetts"),
          func.StrLit("unknown"))

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
          func.ConcatArrays(
            func.MakeArray(guard(ι)),
            func.MakeArray(func.Guard(
              guard(func.ProjectKey(_, func.StrLit("pop"))),
              Type.Coproduct(Type.Int, Type.Coproduct(Type.Dec, Type.Coproduct(Type.Interval, Type.Coproduct(Type.Str, Type.Coproduct(Type.Timestamp, Type.Coproduct(Type.Date, Type.Coproduct(Type.Time, Type.Bool))))))),
              guard(jf => func.Lte(func.ProjectKey(jf, func.StrLit("pop")), func.IntLit(10))),
            func.Undefined)))),
        fix.Filter(_,
          func.ProjectIndex(func.Hole, func.IntLit(1))),
        // FIXME #2034
        // this `Sort` should sort by the representation of the synthetic key "__sd0__"
        fix.Sort(_,
          Nil,
          (func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("pop")), SortDir.asc).wrapNel),
        fix.Reduce(_,
          List(func.MakeMap(StrLit("name"), cond)),
          List(
            ReduceFuncs.First(func.ConcatMaps(
              func.MakeMap(StrLit("name"), cond),
              func.MakeMap(StrLit("__sd__0"), func.ProjectKey(func.ProjectIndex(func.Hole, func.IntLit(0)), func.StrLit("pop")))))),
          func.ConcatArrays(
            func.ConcatArrays(
              func.MakeArray(func.ReduceIndex(0.left)),
              func.MakeArray(func.ReduceIndex(0.right))),
            func.MakeArray(func.ProjectKey(func.ReduceIndex(0.right), func.StrLit("__sd__0"))))),
        // FIXME #2034
        // this `Sort` should sort by the representation of the synthetic key "__sd0__"
        fix.Sort(_,
          Nil,
          (func.ProjectIndex(func.Hole, func.IntLit(2)), SortDir.asc).wrapNel),
        fix.Map(_,
          func.DeleteKey(func.ProjectIndex(func.Hole, func.IntLit(1)), func.StrLit("__sd__0"))))))
    }

    "convert a flattened array" in {
      val lp = fullCompileExp(sqlE"select city, loc[*] from zips")
      val qs = convert(lc.some, lp)

      qs must beSome(beTreeEqual(chainR(
        fix.Read[AFile](rootDir </> file("zips")))(
        fix.LeftShift(_,
          func.Hole,
          IncludeId,
          func.ConcatArrays(
            func.MakeArray(func.ProjectIndex(func.RightSide, func.IntLit(1))),
            func.MakeArray(func.ConcatArrays(
              func.MakeArray(func.ProjectIndex(func.RightSide, func.IntLit(0))),
              func.MakeArray(func.Guard(
                func.ProjectIndex(func.RightSide, func.IntLit(1)),
                Type.Obj(ScalaMap(), Some(Type.Top)),
                func.ProjectKey(
                  func.ProjectIndex(func.RightSide, func.IntLit(1)),
                  func.StrLit("loc")),
                func.Undefined)))))),
        fix.LeftShift(_,
          func.Guard(
            func.ProjectIndex(func.ProjectIndex(func.Hole, func.IntLit(1)), func.IntLit(1)),
            Type.FlexArr(0, None, Type.Top),
            func.ProjectIndex(func.ProjectIndex(func.Hole, func.IntLit(1)), func.IntLit(1)),
            func.Undefined),
          ExcludeId,
          func.ConcatMaps(
            func.MakeMap(
              func.StrLit("city"),
              func.Guard(
                func.ProjectIndex(func.LeftSide, func.IntLit(0)),
                Type.Obj(ScalaMap(), Some(Type.Top)),
                func.ProjectKey(
                  func.ProjectIndex(func.LeftSide, func.IntLit(0)),
                  func.StrLit("city")),
                func.Undefined)),
            func.MakeMap(StrLit("loc"), func.RightSide))))))
    }
  }
}
