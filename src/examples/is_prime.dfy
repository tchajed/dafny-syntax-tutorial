/* The specification for IsPrime. We define 0 and 1 to not be prime here. */

predicate IsPrimeSpec(n: nat) {
  // we define 0 and 1 to not be prime
  n >= 2 &&
  forall i: nat | 2 <= i < n ::
    n % i != 0
}

// illustrate IsPrime on a few examples (note that the verifier is able to check
// these only with some help to find divisors for non-prime numbers)
lemma IsPrimeSpec_tests() {
  assert !IsPrimeSpec(1);
  assert IsPrimeSpec(2);
  assert IsPrimeSpec(3);
  assert 4 % 2 == 0;
  assert !IsPrimeSpec(4);
  assert 6 % 2 == 0;
  assert !IsPrimeSpec(6);
}

/* A recursive implementation of IsPrime. The function HasDivisorAbove checks if
 * n is divisible by something between i and sqrt(n) (see HasDivisorAbove_ok for
 * a precise and verified statement). Note that this is a mathematical
 * optimization: we don't need to check divisors above sqrt(n) because if such a
 * number k divides n, then (n / k) <= sqrt(n) also divides k. A number is prime
 * if it has no divisor, with a special case for n <= 1 to match the spec. */

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
  if n <= 1 then false else
  !HasDivisorAbove(n, 2)
}

/* We'll not prove IsPrime(n) == IsPrimeSpec(n). This will require several helper
 * lemmas: some are due to the use of non-linear arithmetic in the optimization
 * in HasDivisorAbove, others are to handle the recursion. */

lemma square_monotonic(i: nat, j: nat)
  requires 0 < i && i < j
  ensures i * i < j * j
{
  var k: nat := j - i;
  assert j * j == (i + k) * (i + k);
}

// An intermediate spec for what HasDivisorAbove returns, expressed using an
// exists. This just explains what the recursion is doing.
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

// an intermediate lemma about non-linear arithmetic
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

// an intermediate lemma about non-linear arithmetic
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

// This is the main principle for the mathematical optimization: if j is a
// "large" divisor above sqrt(n), then there's also a "small" divisor (n/j).
lemma OtherDivisor(n: nat, j: nat) returns (k: nat)
  requires n > 0 && j > 0
  requires j * j > n
  requires n % j == 0
  // returns n/j so caller names this expression
  ensures k == n / j
  ensures n % k == 0
  ensures k * k <= n
{
  k := n / j;
  mul_mod_0(j, k);
}

lemma IsPrime_ok(n: nat)
  ensures IsPrime(n) == IsPrimeSpec(n)
{
  if n <= 2 {
    return;
  }
  HasDivisorAbove_ok(n, 2);

  if HasDivisorAbove(n, 2) {
    // this case is easy: the divisor proves n is not prime in both IsPrime and
    // IsPrimeSpec
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

  // This is the tricky case: we need a contradiction if j is a divisor that's
  // larger than sqrt(n), because naively it would appear HasDivisorAbove(n, 2)
  // wouldn't find it. OtherDivisor gives us that divisor.

  assert j * j >= n;
  var k := OtherDivisor(n, j);
  assert n % k == 0;
  // we reach a contradiction with !HasDivisorAbove(n, 2)
  assert false;
}
