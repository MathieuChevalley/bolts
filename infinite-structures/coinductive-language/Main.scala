import stainless.lang._
import stainless.collection._

object Main {
  case class Language[A](oo: Boolean, dd: A => Language[A]) {
    def ===(that: Language[A]): Boolean = {
      forall((w: List[A]) => is_member(w,this) == is_member(w,that))
    }
  }

  type Word[A] = List[A]
  
  // checks membership of a word in a language
  def is_member[A](w: List[A], l: Language[A]): Boolean = w match {
    case Nil() => l.oo
    case Cons(x,xs) => is_member(xs, l.dd(x))
  }

  // the empty language
  def zero[A]: Language[A] = Language(false, _ => zero)

  // the language containing only the empty word
  def one[A]: Language[A] = Language(true, _ => zero)

  // the language containing only the letter 'a'
  def atom[A](a: A): Language[A] =
    Language(false, b => if (b == a) one else zero)

  // the union of two languages
  def plus[A](l1: Language[A], l2: Language[A]): Language[A] =
    Language(l1.oo || l2.oo, a => plus(l1.dd(a), l2.dd(a)))

  // zero is neutral for plus
  def plus_zerol[A](l: Language[A]) = {
    plus(zero,l) === l
  } holds

  def plus_zeror[A](l: Language[A]) = {
    plus(l,zero) === l
  } holds

  // plus is associative
  def plus_assoc[A](l1: Language[A], l2: Language[A], l3: Language[A]) = {
    plus(l1,plus(l2,l3)) === plus(plus(l1,l2),l3)
  } holds

  // plus is commutative
  def plus_comm[A](l1: Language[A], l2: Language[A]) = {
    plus(l1,l2) === plus(l2,l1)
  } holds

  // a combination of associativity and commutativity
  def plus_rotate[A](l1: Language[A], l2: Language[A], l3: Language[A]) = {
    plus(l1,plus(l2,l3)) === plus(l2,plus(l1,l3))
  } holds
  
  // plus is idempotent
  def plus_idem[A](l: Language[A]) = {
    plus(l,l) === l
  }
}