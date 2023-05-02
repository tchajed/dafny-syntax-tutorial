function
  HasDivisorAbove(n:nat, i:nat): bool
  decreases n - i
  requires i > 0
{
  if i * i > n then false else
  if n % i == 0 then true else
  HasDivisorAbove(n, i + 1)
}

function
  IsPrime(n: nat): bool {
  if n <= 2 then n == 2 else
  !HasDivisorAbove(n, 2)
}

predicate IsPrimeSpec(n: nat) {
  n >= 2 &&
  forall i: nat | 2 <= i < n ::
    n % i != 0
}

lemma square_monotonic(i: nat, j: nat)
  requires 0 < i && i < j
  ensures i * i < j * j
{
  var k: nat := j - i;
  assert j * j == (i + k) * (i + k);
}

lemma HasDivisorAbove_ok(n: nat, i: nat)
  decreases n - i
  requires i > 0
  ensures HasDivisorAbove(n, i) <==>
          exists j :: && i <= j
                      && j * j <= n
                      && n % j == 0
{
  if i * i > n {
    assert !HasDivisorAbove(n, i); // by definition
    forall j | i < j ensures j * j > n
    {
      square_monotonic(i, j);
    }
  } else {
    HasDivisorAbove_ok(n, i + 1);
  }
}

lemma sum_mod(n: nat, k: nat)
  requires k > 0
  requires n % k == 0
  ensures (n + k) % k == 0
{
  assert k % k == 0;
  assert (n + k) == (n + k) / k * k + (n+k)%k;
  assert n == n / k * k == k * (n/k);
  assert (n + k) == (n/k + 1) * k;
}

lemma mul_mod_0(n: nat, k: nat)
  requires k > 0
  ensures (n * k) % k == 0
{
  if k == 1 || n == 0 {
  } else {
    mul_mod_0(n-1, k);
    assert (n-1) * k + k == n*k;
    sum_mod((n-1) * k, k);
  }
}

lemma OtherDivisor(n: nat, j: nat)
  requires n > 0 && j > 0
  requires j * j > n
  requires n % j == 0
  ensures n % (n / j) == 0
  ensures n / j <= n
{

  mul_mod_0(j, n/j);
}

lemma IsPrime_ok(n: nat)
  ensures IsPrime(n) == IsPrimeSpec(n)
{
  if n <= 2 {
    return;
  }
  HasDivisorAbove_ok(n, 2);

  // this case is easy: the divisor proves n is not prime in both IsPrime and IsPrimeSpec
  if HasDivisorAbove(n, 2) {
    assert IsPrime(n) == IsPrimeSpec(n) == false;
    return;
  }

  // due to no divisor above 2
  assert forall j:nat :: 2 <= j && j * j <= n ==> n % j != 0;

  // if n is actually prime, clearly we didn't find a divisor
  if IsPrimeSpec(n) {
    assert !HasDivisorAbove(n, 2);
    return;
  }

  // consequences of !IsPrimeSpec(n)
  var j: nat :| 2 <= j < n && n % j == 0;
  if j * j < n { return; }
  // this is the tricky case: we need a contradiction if j is a divisor that's
  // larger than sqrt(n), because naively it would appear
  // HasDivisorAbove(n, 2) wouldn't find it

  assert j * j >= n;
  var k := n / j;
  assert n == k * j == j * k;
  assert n % k == 0 && k * k <= n by {
    OtherDivisor(n, j);
  }
}
