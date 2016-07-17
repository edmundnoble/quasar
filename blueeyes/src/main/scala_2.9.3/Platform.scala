// scala 2.9.3
import scalaz._

package blueeyesstubs {
  trait Platform {
    type Duration         = akka.util.Duration
    type ExecutionContext = akka.dispatch.ExecutionContext
    type Future[+A]       = akka.dispatch.Future[A]
    type Promise[A]       = akka.dispatch.Promise[A]

    val Await             = akka.dispatch.Await
    val ExecutionContext  = akka.dispatch.ExecutionContext
    val Future            = akka.dispatch.Future
    val Promise           = akka.dispatch.Promise
    val Duration          = akka.util.Duration

    def futureMonad(ec: ExecutionContext): Monad[Future] = new blueeyes.FutureMonad(ec)
  }
}

package blueeyes {
  class FutureMonad(context: ExecutionContext) extends Applicative[Future] with Monad[Future] {
    def point[A](a: => A): Future[A]                                          = Future(a)(context)
    def bind[A, B](fut: Future[A])(f: A => Future[B]): Future[B]              = fut.flatMap(f)
    override def ap[A, B](fa: => Future[A])(ff: => Future[A => B]): Future[B] = (fa zip ff) map { case (a, f) => f(a) }
  }

  class UnsafeFutureComonad(context: ExecutionContext, copointMaxWait: Duration) extends FutureMonad(context) with Comonad[Future] {
    def copoint[A](m: Future[A])                                  = Await.result(m, copointMaxWait)
    def cojoin[A](a: Future[A]): Future[Future[A]]                = Promise.successful(a)(context)
    def cobind[A, B](fa: Future[A])(f: Future[A] => B): Future[B] = Promise.successful(f(fa))(context)
  }

  object FutureMonad {
    def M(implicit context: ExecutionContext): Monad[Future] = new FutureMonad(context)
  }
}
