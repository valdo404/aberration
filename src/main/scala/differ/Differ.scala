package differ

import differ.DeltaTypes.{Diff}
import shapeless.syntax.std.tuple._
import shapeless.{::, CNil, Generic, HList, HNil, Inl, Inr, Lazy, _}

trait Delta[In] {
  type Out

  def apply(before: In, after: In): Diff[Out]
}

object DeltaTypes {
  import shapeless.ops.hlist._
  object changed extends Poly1 {
    implicit def caseGroup[T] = at[GroupDiff[T]](_.isChange)
    implicit def caseId[T] = at[NoDiff[T]](_ => false)
    implicit def caseContent[T] = at[ContentDiff[T]](_ => false)
    implicit def caseAdded[T] = at[Added[T]](_ => true)
    implicit def caseRemoved[T] = at[Removed[T]](_ => true)
  }

  trait Diff[T] {
    def isChange: Boolean
  }
  case class NoDiff[T]() extends Diff[T] {
    def isChange = false
  }

  trait ChangedDiff[T] extends Diff[T] {
    def isChange = true
    val t: T
  }

  case class GroupDiff[T](hlist: HList) extends Diff[T] {

    override def isChange() = {
      true
    }
  }
  case class ContentDiff[T](t: T) extends ChangedDiff[T]
  case class Added[T](t: T) extends ChangedDiff[T]
  case class Removed[T](t: T) extends ChangedDiff[T]
}

trait Delta0 {
  import DeltaTypes._

  implicit def generic[F, G](
    implicit gen: Generic.Aux[F, G],
    genDelta: Lazy[Delta[G]]
  ): Delta.Aux[F, genDelta.value.Out] = new Delta[F] {
    type Out = genDelta.value.Out

    def apply(before: F, after: F): Diff[Out] =
      genDelta.value.apply(gen.to(before), gen.to(after))
  }
}

object Delta extends Delta0 {
  import DeltaTypes._
  def apply[In](
    implicit delta: Lazy[Delta[In]]
  ): Delta.Aux[In, delta.value.Out] = delta.value

  type Aux[In, Out0] = Delta[In] { type Out = Out0 }

  implicit val booleanDelta =
    new Delta[Boolean] {
      type Out = Boolean

      def apply(before: Boolean, after: Boolean): Diff[Out] = {
        if (before != after) ContentDiff(before == after) else NoDiff[Out]()
      }
    }

  implicit val intDelta = new Delta[Int] {
    type Out = Int

    def apply(before: Int, after: Int): Diff[Out] =
      if (before != after) ContentDiff(after - before) else NoDiff[Out]()
  }

  implicit val longDelta = new Delta[Long] {
    type Out = Long

    def apply(before: Long, after: Long): Diff[Out] =
      if (before != after) ContentDiff(after - before) else NoDiff[Out]()
  }

  implicit def mapDelta[T, U](implicit deltaU: Lazy[Delta[U]]) =
    new Delta[Map[T, U]] {
      type Out =
        Seq[Diff[(T, U)]] :: Seq[Diff[(T, U)]] :: Map[T, deltaU.value.Out] :: HNil

      def apply(before: Map[T, U], after: Map[T, U]): Diff[Out] = {
        type BeforeAnalysis =
          Seq[Removed[(T, U)]] :: Map[T, Diff[deltaU.value.Out]] :: HNil

        def analyzeOne(current: (T, U),
                       after: Map[T, U],
                       agg: BeforeAnalysis): BeforeAnalysis = {
          val removedKeys :: diff :: HNil = agg
          val (key, value) = current

          if (after.contains(key)) {
            val tuple =
              (key, deltaU.value.apply(value, after(key)))

            removedKeys :: (diff + tuple) :: HNil
          } else {
            (removedKeys :+ Removed[(T, U)](current)) :: diff :: HNil
          }
        }

        val emptyValue = Seq
          .empty[Removed[(T, U)]] :: Map
          .empty[T, Diff[deltaU.value.Out]] :: HNil

        val (removed: Seq[Diff[(T, U)]]) :: (changed: Map[T, deltaU.value.Out]) :: HNil =
          before.foldLeft(emptyValue) {
            case (agg: BeforeAnalysis, current: (T, U)) =>
              analyzeOne(current, after, agg)
          }

        val added: Seq[Added[(T, U)]] = after.collect {
          case (key, value) if !before.contains(key) => Added((key, value))
        }.toSeq

        //if (before == after)
        //  Id[Out]()
        //else
        ContentDiff(removed :: added :: changed.filterNot {
          case (k, n: NoDiff[T]) => true
          case _                 => false
        } :: HNil)
      }
    }

  implicit def stringDelta =
    new Delta[String] {
      type Out = (String, String)

      def apply(before: String, after: String): Diff[(String, String)] =
        if (before != after)
          ContentDiff((before, after))
        else
          NoDiff()
    }

  implicit def optionDelta[T](implicit deltaT: Lazy[Delta[T]]) =
    new Delta[Option[T]] {
      type Out = Option[HList] :+: Option[deltaT.value.Out] :+: T :+: T :+: CNil

      def apply(before: Option[T], after: Option[T]): Diff[Out] =
        (before, after) match {
          case (None, None) => NoDiff()
          case (Some(b), Some(a)) =>
            deltaT.value
              .apply(b, a) match {
              case i: NoDiff[T] =>
                NoDiff()
              case c: ContentDiff[T] =>
                ContentDiff(Inr(Inl(Some(c.t))))
              case c: GroupDiff[T] =>
                ContentDiff(Inl(Some(c.hlist)))
            }
          case (Some(b), None) => Removed(Inr(Inr(Inl(b))))
          case (None, Some(a)) => Added(Inr(Inr(Inr(Inl(a)))))
        }
    }

  implicit def someDelta[T](
    implicit deltaT: Lazy[Delta[Some[T]]]
  ): Delta[Some[T]] = new Delta[Some[T]] {
    override type Out = deltaT.value.Out

    override def apply(before: Some[T], after: Some[T]): Diff[Out] =
      deltaT.value.apply(before, after)
  }

  implicit def deriveHNil = new Delta[HNil] {
    type Out = HNil

    def apply(before: HNil, after: HNil): Diff[HNil] = NoDiff()
  }

  implicit def deriveHCons[H, T <: HList](
    implicit deltaH: Delta[H],
    deltaT: Lazy[Delta[T] { type Out <: HList }]
  ): Delta.Aux[H :: T, deltaH.Out :: deltaT.value.Out] = new Delta[H :: T] {
    type Out = deltaH.Out :: deltaT.value.Out

    def apply(before: H :: T, after: H :: T): Diff[Out] = {
      val headDiff = deltaH.apply(before.head, after.head)

      before.tail match {
        //case _: HNil => GroupChanged[deltaH.Out :: deltaT.value.Out](HNil)
        case _ =>
          val tailDiff = deltaT.value.apply(before.tail, after.tail)

          tailDiff match {
            case c: GroupDiff[T] =>
              GroupDiff[deltaH.Out :: deltaT.value.Out](headDiff :: c.hlist)
            case c @ _ =>
              GroupDiff[deltaH.Out :: deltaT.value.Out](headDiff :: c :: HNil)
          }
      }
    }
  }
}

object DeltaSyntax {
  import DeltaTypes._

  implicit class DeltaOps[In](val before: In) extends AnyVal {
    def delta(
      after: In
    )(implicit delta: Lazy[Delta[In]]): Diff[delta.value.Out] =
      delta.value(before, after)
  }
}
