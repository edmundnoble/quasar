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

package quasar.qscript.qsu

import slamdata.Predef.{Map => SMap, _}
import quasar.contrib.scalaz.{MonadError_, MonadState_}
import quasar.ejson
import quasar.ejson.EJson
import quasar.ejson.implicits._
import quasar.fp._
import quasar.qscript.provenance._

import matryoshka._
import matryoshka.data._
import matryoshka.implicits._
import pathy.Path
import scalaz.{Free, IList, Monad, StateT}
import scalaz.syntax.foldable1._
import scalaz.syntax.monad._

final class ApplyProvenance[T[_[_]]: BirecursiveT: EqualT] {
  import ApplyProvenance._
  import QScriptUniform._

  type P = QProv.P[T]
  type Dims = Dimensions[P]
  type QSU[A] = QScriptUniform[T, A]

  type GPF[A] = QSUGraph.QSUPattern[T, A]
  val GPF = QSUGraph.QSUPattern

  type GStateM[F[_]] = MonadState_[F, QSUGraph[T]]
  def GStateM[F[_]](implicit ev: GStateM[F]): GStateM[F] = ev

  // TODO: Real errors
  type ErrorM[F[_]] = MonadError_[F, String]
  def ErrorM[F[_]](implicit ev: ErrorM[F]): ErrorM[F] = ev

  val dims = QProv[T]

  def apply[F[_]: Monad: ErrorM](graph: QSUGraph[T]): F[AuthenticatedQSU[T]] = {
    type X[A] = StateT[F, QSUGraph[T], A]
    graph.elgotZygoM(computeProvenanceƒ[X], applyProvenanceƒ[X])
      .run(graph)
      .map { case (g, (_, d)) => AuthenticatedQSU(g, d) }
  }

  def applyProvenanceƒ[F[_]: Monad: GStateM]: ElgotAlgebraM[(Dims, ?), F, GPF, (Symbol, QSUDims[T])] = {
    case (updDims, GPF(deId, DimEdit((srcId, qdims), _))) =>
      val srcDims = dims.rename(deId, srcId, updDims)
      GStateM[F].modify(_.replace(deId, srcId))
        .as((srcId, qdims + (srcId -> srcDims)))

    case (nodeDims, GPF(nodeId, node)) =>
      (nodeId, node.foldRight[QSUDims[T]](SMap(nodeId -> nodeDims))(_._2 ++ _)).point[F]
  }

  def computeProvenanceƒ[F[_]: Monad: ErrorM]: AlgebraM[F, GPF, Dims] =
    gpf => gpf.qsu match {
      case AutoJoin(srcs, _) => srcs.foldLeft1(dims.join(_, _)).point[F]

      case DimEdit(src, DTrans.Squash()) => dims.squash(src).point[F]

      case DimEdit(src, DTrans.Group(k)) =>
        dims.swap(0, 1, dims.lshift(k as gpf.root, src)).point[F]

      case Distinct(src) => src.point[F]

      case GroupBy(_, _) => unexpectedError("GroupBy", gpf.root)

      case JoinSideRef(_) => unexpectedError("JoinSideRef", gpf.root)

      case LeftShift(_, _, _, _) => unexpectedError("LeftShift", gpf.root)

      case LPFilter(src, _) => unexpectedError("LPFilter", gpf.root)

      case LPJoin(_, _, _, _, _, _) => unexpectedError("LPJoin", gpf.root)

      case LPReduce(src, _) => dims.reduce(src).point[F]

      case QSFilter(src, _) => src.point[F]

      case QSReduce(src, _, _, _) => dims.reduce(src).point[F]

      case Map(src, _) => src.point[F]

      case Nullary(_) => dims.empty.point[F]

      case Read(file) => dims.squash(segments(file).map(projStr).reverse).point[F]

      case Sort(_, _) => unexpectedError("Sort", gpf.root)

      case Subset(from, _, count) => dims.join(from, count).point[F]

      case ThetaJoin(left, right, _, _, _) => dims.join(left, right).point[F]

      case Transpose(src, rot) =>
        val tid: dims.I = Free.pure(gpf.root)
        (rot match {
          case Rotation.ShiftMap   | Rotation.ShiftArray   => dims.lshift(tid, src)
          case Rotation.FlattenMap | Rotation.FlattenArray => dims.flatten(tid, src)
        }).point[F]

      case UniformSort(src, _, _) => src.point[F]

      case Union(left, right) => dims.union(left, right).point[F]
    }

  ////

  private def projStr(s: String): P =
    dims.prov.proj(ejson.CommonEJson(ejson.Str[T[EJson]](s)).embed)

  private def segments(p: Path[_, _, _]): IList[String] = {
    val segs = Path.flatten[IList[String]](IList(), IList(), IList(), IList(_), IList(_), p)
    (segs.head :: segs.tail).join
  }

  private def unexpectedError[F[_]: ErrorM, A](nodeName: String, id: Symbol): F[A] =
    ErrorM[F].raiseError(s"ComputeProvenance: Encountered unexpected $nodeName[$id].")
}

object ApplyProvenance {
  def apply[T[_[_]]: BirecursiveT: EqualT]: ApplyProvenance[T] =
    new ApplyProvenance[T]

  final case class AuthenticatedQSU[T[_[_]]](
      graph: QSUGraph[T],
      dims: QSUDims[T])
}