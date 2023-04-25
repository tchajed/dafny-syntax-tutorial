/*
Outline:
- recursion
- opacity
- assign-such-that
- bisection debugging
*/

opaque ghost predicate Good(n: nat) {
  n > 3
}

lemma FourIsGood()
  ensures Good(4)
{
  reveal Good();
}

lemma GoodMonotonic(n: nat, m: nat)
  requires Good(n) && m >= n
  ensures Good(m)
{
  reveal Good();
}

lemma SevenIsGood()
  ensures Good(7)
{
  FourIsGood();
  GoodMonotonic(4, 7);
}
