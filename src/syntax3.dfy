/* This lecture covers some advanced features. They aren't really related to each other.

- Opacity and revealing
- Recursive functions and lemmas
- assign-such-that
*/


/* **Opacity** */

/* Sometimes verification doesn't work or is too slow, especially when many
 * `forall` expressions are involved. One way to make it faster and more
 * predictable is to use _opacity_, which temporarily hides the body of a
 * definition from the verification engine. With an opaque definition we can
 * write a collection of lemmas that _reveal_ the body and use it directly, but
 * thereafter use only those lemmas rather than the body directly. This can be
 * much more efficient if we only need those limited properties and not
 * everything about the body, and also because Dafny only needs to check the
 * lemmas once and then can assume them for other proofs. */


/* We'll illustrate the mechanisms with this `Good` predicate. The predicate
 * isn't actually complicated, but using it opaquely will illustrate how the
 * mechanisms work. */

opaque ghost predicate Good(n: nat) {
  n > 3
}

lemma FourIsGood_attempt1()
  ensures Good(4)
{
  // notice that this proof doesn't go through - Dafny doesn't know anything
  // about Good other than it is a deterministic predicate that takes a `nat`.
}

lemma FourIsGood()
  ensures Good(4)
{
  // New feature (reveal statement): we can reveal the body of an opaque
  // predicate. After that its body is available to the proof.
  reveal Good();
}

// Here's a property `Good` satisfies which doesn't quite reveal everything
// about it.
lemma GoodMonotonic(n: nat, m: nat)
  requires Good(n) && m >= n
  ensures Good(m)
{
  reveal Good();
}

// Now we can prove 7 is good without knowing exactly what `Good` means.
lemma SevenIsGood()
  ensures Good(7)
{
  FourIsGood();
  GoodMonotonic(4, 7);
}


/* **Recursion** */

/* Dafny supports recursive functions and lemmas. The one caveat is that we need
 * to prove that they terminate. */

function fibonacci(n: nat): nat
  // `decreases n` says that we promise to call `fibonacci` recursively only on
  // arguments (strictly) smaller than `n`. Because `n` can only go down to 0,
  // this ensures that the function eventually terminates.
  decreases n
{
  if n <= 1 then 1 else fibonacci(n-1) + fibonacci(n-2)
}

lemma Fibonacci_examples()
{
  assert fibonacci(0) == 1;
  assert fibonacci(1) == 1;
  assert fibonacci(2) == 2;
  assert fibonacci(3) == 3;
  assert fibonacci(4) == 5;
}

/* We can prove properties about fibonacci using induction. It turns out
 * induction is the same thing as a recursive lemma (!), and that's exactly how
 * Dafny supports it. */

/* We'll start with this arbitrary property - the nth fibonacci number is at
 * least n. */

// You can ignore the {:induction false} - it disables some automation in Dafny
// that obscures what's going on.
lemma {:induction false} FibonacciGreater(n: nat)
  // Just like the function, we'll need to call this lemma recursively only on
  // smaller `n`. It's easier to see why this is important - if we didn't, then
  // we could have a circular proof and would be able to prove anything by just
  // calling our own lemma in an infinite loop! That would make Dafny unsound
  // and thus fairly useless for doing proofs.
  decreases n
  ensures fibonacci(n) >= n
{
  if n <= 1 {
    // the base cases are easy
  } else {
    FibonacciGreater(n-1);
    FibonacciGreater(n-2);
    // What we actually know is that fibonacci(n) >= n-1 + n-2 = 2*n-3.
    assert fibonacci(n) >= n-1 + n-2;

    // We need this expression to be at least n, but that isn't true for n=2. In
    // that case the postcondition does hold if we just manually compute
    // fibonacci(2), and for higher n we can use induction.
    if n == 2 {
      assert fibonacci(n) == 2;
      assert fibonacci(n) >= n;
    } else {
      assert 2*n-3 >= n;
    }

    // (If you remove the entire `if` statement above you'll actually find Dafny
    // can do all of that reasoning automatically.)
  }
}
