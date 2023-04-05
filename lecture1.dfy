/* Mathematical assertions */
lemma SomeAssertions() {
  assert 2 + 2 == 4;
  assert 1 < 2;
  assert -3*-2 == -6;
  assert 1 + 2*3 == 7;
}

/* a function is a mathematical function: it is always deterministic, and is
  written without mutable variables or data structures */

function abs(x: int): int {
  /* if is an expression */
  if x < 0 then -x else x
}

/* We can prove things about functions using lemmas.

   This lemma has a parameter. When we use the lemma, that parameter is just
   like a function argument: we'll call AbsLarger on some specific x.
 */
lemma AbsLarger(x: int)
  ensures abs(x) >= x
{}

/* this property isn't true */
lemma AbsStrictlyLarger(x: int)
  ensures abs(x) > x
{
  // we can invoke the already-proven lemma like this - but it doesn't actually
  // help prove the postcondition in this case
  AbsLarger(x);
  // Next we could try splitting the proof into two cases, which looks just like
  // an if statement in imperative code.
  if x < 0 {
    // there's no error here! the postcondition actually does hold on this path
  } else {
    // But here if we think about it we realize abs(x) == x.
    assert abs(x) == x;
  }
}

lemma AbsNegLarger(x: int)
  requires x < 0
  ensures abs(x) > x
{}

/* Quantifiers */

lemma AbsLargerForAll()
  ensures forall x: int :: abs(x) >= x
{
  // new syntax: forall statement
  forall x: int
    ensures abs(x) >= x
  {
    // this statement allows us to refer to x when proving a forall, which means
    // we can call lemmas, do `if` case splits, etc.
    AbsLarger(x);
  }
}

/* This lemma shows, in a roundabout way, that positive numbers have a negative
 * with the same absolute value. */
lemma PosHasNeg(x: int)
  requires x > 0
  ensures exists y :: y < 0 && abs(y) == x
{
  // Dafny needs some help here to find a "witness" for y, which proves the
  // exists. In this case it's pretty simple to see that the y that exists is
  // -x.
  var y := -x;
  // This assertion nudges Dafny along to use y to prove the postcondition. Not
  // all of this is necessary but it's good practice.
  assert y < 0 && abs(y) == x;
}

/* TODO: assign such that? what would the example be? */
