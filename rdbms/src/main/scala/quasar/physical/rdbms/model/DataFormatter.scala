/*
 * Copyright 2014–2018 SlamData Inc.
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

package quasar.physical.rdbms.model

import slamdata.Predef._
import quasar.Data

trait DataFormatter {

  def apply(n: String, d: Data): String

}

object DataFormatter {

  def apply(f: (String, Data) => String): DataFormatter = new DataFormatter {
    def apply(n: String, d: Data) = f(n, d)
  }

}