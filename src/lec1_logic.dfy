/* Mathematical reasoning in Dafny */

/*** Mathematical assertions ***/
// {{{

/* The first bit of Dafny we introduce are lemmas and assertions. A lemma is
 * like a method or procedure in other languages. Unlike in other languages,
 * Dafny will statically check each assertion in a lemma and report an error if
 * it cannot prove it. This is similar to how the compiler checks your types and
 * reports an error if they don't match. */

lemma SomeAssertions() {
  assert 2 + 2 == 4;
  assert 1 < 2;
  // this one is wrong
  // assert -3*-2 == -6; // error: assertion might not hold
  assert 1 + 2*3 == 7;
}

/* Here are a few more built-in Dafny operators, which are used for stating
 * logical facts: */

lemma LogicalOperators() {
  assert true && (true || false);
  assert true == false || true;
  // Dafny has a boolean implies operator written p ==> q. As you might recall,
  // p ==> q is the same as !p || q. Implications are quite common when writing
  // logical properties.
  assert !(true ==> false);
  assert false ==> false;
  // Dafny also has a boolean "if and only if" operator. This is identical to ==
  // for booleans, but it often conveys intent better when used for assertions.
  assert false <==> false;
  assert !(true <==> false);
}
// }}}


/*** Functions ***/
// {{{

/* A Dafny `function` is a mathematical function: it is always deterministic, and
 * is written without mutable variables or data structures. Functions are one way
 * to define something interesting to prove properties about in Dafy. In the next
 * lecture we'll see datatypes (both built-in and user-defined) which will give
 * us a lot more to play with. */

function Enlargen(x: int): int {
  2 * x + 5
}

function IsLarge(x: int): bool {
  x > 1000
}

// New feature (predicate): `predicate` is a shorthand for a function that
// returns a boolean.  Functions that return a boolean are extremely common in
// verification since they express logical predicates, hence the special syntax.
predicate IsSmall(x: int) {
  !IsLarge(x)
}

predicate LocalVars(b: bool, i1: int, i2: int) {
  // New feature (function local variables): we can create (immutable) local
  // variables to break up large function definitions
  var larger := i1 > i2;
  !b && larger
}

function abs(x: int): int {
  // New feature (if expression): in a function, `if` is an _expression_ in
  // Dafny. We'll see `if` _statements_ in lemmas later.
  if x < 0 then -x else x
}

// }}}


/*** Lemmas ***/
// {{{

/* We can prove things about functions using lemmas. A lemma has parameters, an
 * optional _requires_ clause (its precondition) and an _ensures_ clause (its
 * postcondition). */

// This lemma has a parameter. When we use the lemma, that parameter is just
// like a function argument: we'll call `AbsLarger` on some specific x.
lemma AbsLarger(x: int)
  ensures abs(x) >= x
{}

// This lemma isn't true, but its proof and Dafny's reported errors will be
// instructive.
lemma AbsStrictlyLarger_attempt(x: int)
  ensures abs(x) > x
{
  // we can invoke the already-proven lemma like this - but it doesn't actually
  // help prove the postcondition in this case
  AbsLarger(x);
  // New feature (lemma if statement): to split a proof into cases, we can use
  // an _if statement_, which looks just like an imperative `if` statement in many
  // other languages.
  if x < 0 {
    // there's no error here! the postcondition actually does hold on this path
  } else { // error: a postcondition could not be proved on this return path
    // But here, if we think about it, we realize abs(x) == x.
    assert abs(x) == x;
  }
}

/* Based on what we learned in the proof of AbsStrictlyLarger, here's a lemma
 * that does verify. */

lemma AbsNegLarger(x: int)
  requires x < 0
  ensures abs(x) > x
{}

/* The statement of a lemma (its pre- and post-condition) is an _abstraction
 * boundary_ in Dafny that divides the body from the "outside world" (all the
 * code that uses the lemma). The body of a lemma is used to prove its
 * postcondition, assuming its precondition; outside of the body, Dafny will
 * ignore the body.  */
// }}}


/*** Quantifiers ***/
// {{{

/* Dafny has a `forall` logical expression that can be used in assertions, with
 * the expected meaning. It can prove such assertions automatically in many
 * cases: */

lemma ForallAssertionExamples()
{
  // These assertions are different from what we'd normally have in a
  // programming language because they aren't _executable_. These are
  // mathematical assertions that can be checked statically, but not by simply
  // running them since they talk about all integers.
  assert forall x: int :: x + 1 > x;
  assert forall x: int, y: int :: x + y == y + x;
  assert forall b: bool :: b || !b;
}

/* Here's an example of proving a forall: */

lemma AbsLargerForAll()
  ensures forall x: int :: abs(x) >= x
{
  // New feature (forall statement): a _forall statement_ allows us to help Dafny with a proof of
  // `forall x :: ...` by talking about an individual `x` */
  forall x: int
    ensures abs(x) >= x
  {
    // Within the body of a forall statement, the proof can refer to `x` when
    // proving the ensures clause, which means we can call lemmas, do `if` case
    // splits, etc.
    AbsLarger(x);
  }
}

/* Dafny also has an `exists` quantifier. */

// This lemma shows, in a roundabout way, that positive numbers have a negative
// with the same absolute value.
lemma PosHasNeg(x: int)
  requires x > 0
  ensures exists y :: y < 0 && abs(y) == x
{
  // Dafny needs some help here to find a "witness" for y, which proves the
  // exists. In this case it's pretty simple to see that the y that exists is
  // -x.
  var y := -x;
  // This assertion nudges Dafny along to use y to prove the postcondition.
  assert y < 0 && abs(y) == x;
}

// }}}
