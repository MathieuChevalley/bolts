import stainless.lang._
import stainless.collection._

object Main {
  type Word[A] = List[A]

  case class Lang[A](oo: Boolean, dd: A => Lang[A]) {
    def ===(that: Lang[A]): Boolean = {
      forall((w: List[A]) => this.contains(w) == that.contains(w))
    }

    def contains(w: Word[A]): Boolean = w match {
      case Nil() => oo
      case Cons(x,xs) => dd(x).contains(xs)
    }

    // union
    def +(that: Lang[A]): Lang[A] =
      Lang(this.oo || that.oo, a => this.dd(a) + that.dd(a))

    // concatenation
    def $(that: Lang[A]): Lang[A] = 
      Lang(this.oo && that.oo, a =>
        if (this.oo) 
          (this.dd(a) $ that) + that.dd(a)
        else 
          this.dd(a) $ that
      )

    // intersection
    def n(that: Lang[A]): Lang[A] = 
      Lang(this.oo && that.oo, a => this.dd(a) n that.dd(a))

    // Kleene iteration
    def star: Lang[A] =
      Lang(true, a => this.dd(a) $ star)

    // complement
    def c: Lang[A] =
      Lang(!oo, a => dd(a).c)

    // shuffle operator
    def |(that: Lang[A]): Lang[A] =
      Lang(this.oo && that.oo, a =>
        (this.dd(a) | that) +
        (this | that.dd(a))
      )
  }

  // the empty Lang
  def zero[A]: Lang[A] = Lang(false, _ => zero)

  // the language containing only the empty word
  def one[A]: Lang[A] = Lang(true, _ => zero)

  // the language containing only the letter 'a'
  def atom[A](a: A): Lang[A] =
    Lang(false, b => if (b == a) one else zero)

  // the full language
  def full[A]: Lang[A] = Lang(true, _ => full)

  // zero is neutral for plus
  def plus_zerol[A](l: Lang[A]) = {
    zero + l === l
  } holds

  def plus_zeror[A](l: Lang[A]) = {
    l + zero === l
  } holds

  def plus_dd[A](l1: Lang[A], l2: Lang[A], x: A): Boolean = {
    (l1 + l2).dd(x) == l1.dd(x) + l2.dd(x)
  } holds

  def plus_lemma[A](l1: Lang[A], l2: Lang[A], w: Word[A]): Boolean = {
    assert(
      w match {
        case Nil() => true
        case Cons(x,xs) => plus_lemma(l1.dd(x), l2.dd(x), xs) // induction hypothesis
      }
    )
    (l1 + l2).contains(w) == (l1.contains(w) || l2.contains(w))
  } holds

  // plus is associative (contains)
  def plus_assoc_lemma[A](l1: Lang[A], l2: Lang[A], l3: Lang[A], w: Word[A]) = {
    assert(plus_lemma(l1,l2,w))
    assert(plus_lemma(l2,l3,w))
    assert(plus_lemma(l1,l2 + l3,w))
    assert(plus_lemma(l1 + l2,l3,w))
    (l1 + (l2 + l3)).contains(w) == ((l1 + l2) + l3).contains(w)
  } holds

  // plus is associative
  def plus_assoc[A](l1: Lang[A], l2: Lang[A], l3: Lang[A]) = {
    assert(forall((w: Word[A]) => {
      assert(plus_assoc_lemma(l1,l2,l3,w))
      (l1 + (l2 + l3)).contains(w) == ((l1 + l2) + l3).contains(w)
    }))
    l1 + (l2 + l3) === (l1 + l2) + l3
  } holds

  // plus is commutative (contains)
  def plus_comm_lemma[A](l1: Lang[A], l2: Lang[A], w: Word[A]) = {
    plus_lemma(l1,l2,w)
    plus_lemma(l2,l1,w)
    (l1 + l2).contains(w) == (l2 + l1).contains(w)
  } holds

  // plus is commutative
  def plus_comm[A](l1: Lang[A], l2: Lang[A]) = {
    assert(forall((w: Word[A]) => {
      assert(plus_comm_lemma(l1,l2,w))
      (l1 + l2).contains(w) == (l2 + l1).contains(w)
    }))
    l1 + l2 === l2 + l1
  } holds

  // a combination of associativity and commutativity
  def plus_rotate[A](l1: Lang[A], l2: Lang[A], l3: Lang[A]) = {
    assert(plus_assoc(l1,l2,l3))
    assert(plus_comm(l1,l2))
    assert(plus_assoc(l2,l1,l3))
    l1 + (l2 + l3) === l2 + (l1 + l3)
  } holds
  
  // plus is idempotent
  def plus_idem[A](l: Lang[A]) = {
    assert(forall((w: Word[A]) => {
      assert(plus_lemma(l,l,w))
      (l + l).contains(w) == l.contains(w)
    }))
    l + l === l
  } holds
  
  // a combination of associativity and idempotence
  def plus_idem_assoc[A](l1: Lang[A], l2: Lang[A]) = {
    assert(plus_assoc(l1,l1,l2))
    assert(plus_idem(l1))
    l1 + (l1 + l2) === l1 + l2
  } holds

  // union with one does nothing when oo is true
  def plus_one_l[A](l: Lang[A]) = {
    require(l.oo)

    one + l === l
  } holds

  // union with one does nothing when oo is true
  def plus_one_r[A](l: Lang[A]) = {
    require(l.oo)

    l + one === l
  } holds

  // concatenation with the empty Lang is empty
  def times_zero_l[A](l: Lang[A]) = {
    (zero $ l) === zero
  } holds

  // concatenation with the empty Lang is empty
  def times_zero_r[A](l: Lang[A]) = {
    (l $ zero) === zero
  } holds

  // one is neutral for concatenation
  def times_one_l[A](l: Lang[A]) = {
    (one $ l) === l
  } holds

  // one is neutral for concatenation
  def times_one_r[A](l: Lang[A]) = {
    (l $ one) === l
  } holds

  // // distributivity on the left
  // def times_plus_l[A](l1: Lang[A], l2: Lang[A], l3: Lang[A]) = {
  //   (l1 + l2) * l3 === (l1 * l3) + (l2 * l3)
  // } holds

  // // distributivity on the right
  // def times_plus_r[A](l1: Lang[A], l2: Lang[A], l3: Lang[A]) = {
  //   l1 * (l2 + l3) === (l1 * l2) + (l1 * l3)
  // } holds

  // // associativity of concatenation
  // def times_assoc[A](l1: Lang[A], l2: Lang[A], l3: Lang[A]) = {
  //   l1 * (l2 * l3) === (l1 * l2) * l3
  // } holds
}