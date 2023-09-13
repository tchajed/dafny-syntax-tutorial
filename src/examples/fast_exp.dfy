function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    return;
  } else {
    exp_sum(b, n1-1, n2);
  }
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  ghost var n0 := n;
  var n := n;
  ghost var i := 0;
  while n > 0
    decreases n
    invariant c == exp(b, exp(2, i))
  {
    if n % 2 == 1 {
      // a accumulates sum(i => b^(2^n_i), i) where n_i are the 1 bits of n
      // TODO: n-n0 is sum(i => 2^n_i, i), right?
      a := a * c;
      // (n-1)/2 == n/2 in this case, but we want to be extra clear that we're
      // "dropping" a 1 bit here and so something interesting is happening
      n := (n-1) / 2;
    } else {
      n := n / 2;
    }
    c := c * c;
    exp_sum(b, exp(2, i), exp(2, i));
    i := i + 1;
  }
  assert false;
  return a;
}
