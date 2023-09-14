/* More interesting data to reason about: sequences. */

/* In order to write proofs about interesting systems and protocols, we first
 * need some way of modeling the state of those systems and protocols. We'll
 * explore Dafy's built-in sequence type as well as algebraic data types, its
 * core way of creating user-defined types. */

/*** Sequences ***/
// {{{

/* These data types are very similar to data structures, but will be purely
 * mathematical. We'll start with the sequence type `seq<T>`. The `T` in angle
 * brackets is a _type parameter_, needed because sequences can hold values of
 * any type. A sequence is related to data structures you're familiar with like
 * linked lists or arrays/vectors (the terminology depends on the programming
 * language). A sequence is the mathematical essence of the state of a
 * list/vector/array without the implementation details.
 */

lemma BasicSequences()
{
  var s: seq<nat> := [1, 17, 3];
  assert s[1] == 17;
}

lemma SequenceOperations()
{
  // var is a (mutable) local variable, defined within a lemma
  var s: seq<int> := [3, 1, 2];
  // sequences can be indexed, starting at 1
  assert s[1] == 1;
  // we can extract a subsequence
  assert s[1..2] == [1];
  // we can re-assign the sequence and update one element using the `s[i := v]` syntax.
  s := s[2 := 3];
  assert s[0] == s[2] == 3;
  // `|s|` is the sequence's length
  assert |s| == 3;
  // we can append two sequences
  s := s + [7, 12];
  assert |s| == 5;
  assert s == [3, 1, 3, 7, 12];
}

/* Below we give some lemmas illustrating sequence operations. */
// {{{

function SeqGet(s: seq<int>, i: nat): int
  // New feature (function preconditions): functions can have _requires_
  // clauses, also called _preconditions_. Dafny will statically check  that the
  // preconditions hold (in the same way as assertions) wherever a call to the
  // function appears.
  //
  // This particular precondition requires that the index is in-bounds. The fact
  // that `i` is of type `nat` already assures that it is non-negative.
  requires i < |s|
{
  s[i]
}

function SeqUpdate(s: seq<int>, i: nat, n: int): seq<int>
  requires i < |s|
{
  s[i := n]
}

lemma CheckedPreconditions(s: seq<int>, i: nat)
  // Dafny does not allow even stating this because it tries to index a //
  // sequence without a proof that the index is in-bounds, one of the preconditions
  // for sequence indexing.
  //
  // We'd get the same error in an ensures clause or function definition.
  requires s[i] > 0 // error: index out of range
{}

lemma CheckedFunctionPreconditions(s: seq<int>, i: nat)
  // almost same as above, but notice that the error specifically points to the
  // `SeqGet` precondition
  requires SeqGet(s, i) > 0 // error: function precondition could not be proved
{}

lemma SequenceAppendFact(s1: seq<int>, s2: seq<int>)
  // New feature (forall where clause): notice the new pipe symbol after the `i`.
  // The general syntax is of the form `forall x | p(x) :: q(x)`; it means the
  // same thing as `forall x :: p(x) ==> q(x)` but can be easier to read. You
  // might read this as "for all x where p(x), q(x)".
  //
  // We're also leaving off the type of `i` because Dafny can infer that it's an `int`.
  ensures forall i | |s1| <= i < |s1| + |s2| :: (s1 + s2)[i] == s2[i - |s1|]
{ // goes through without any extra proof
}

// }}}

// }}}
