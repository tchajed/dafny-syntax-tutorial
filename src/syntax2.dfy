/* Outline:

- sequences
- algebraic data types
- recursion
*/

function SeqGet(s: seq<int>, i: nat): int
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
  // Dafny does not allow even stating this because it tries to index a
  // sequence without a proof that the index is in-bounds.
  //
  // We'd get the same error in an ensures clause or function definition.
  requires s[i] > 0
{}

lemma SequenceAppendFact(s1: seq<int>, s2: seq<int>)
  ensures forall i | |s1| <= i < |s1| + |s2| :: (s1 + s2)[i] == s2[i - |s1|]
{
  // goes through without any extra proof
}
