/* Review of logical connectives and properties of first-order logic. */

/* We'll be using boolean logic both to define protocols and to state their
 * properties, so it helps if you have an understanding of what the connectives
 * of logic mean and have a little fluency with manipulating them. */

/* The core of logic is the _proposition_. For us, a proposition like `2 < 3` is
 * going to be a boolean, with the interpretation that the proposition is true,
 * well, if the boolean is true, and false if not. That proposition is clearly
 * true.
 */

lemma ExampleProposition()
{
  assert 2 < 3;
}

/* Another example: `7 - 3 == 3` is clearly false, but it's still a
 * proposition.
 */
lemma SomethingFalse()
{
  // you'll get an error if you uncomment this line
  // assert 7 - 3 == 3;
}

/* On the other hand something like `7 * false < 8` isn't a
 * proposition at all since it has a type error - we won't have to worry too
 * much about these because Dafny will quickly and easily catch such mistakes.
 */
lemma SomethingNonsensical()
{
  // you'll get an error if you uncomment this line
  //
  // unlike the above, it will be a type-checking error and not a verification
  // failure
  // assert 7 * false < 8;
}

/* In Dafny, we can write lemmas with arguments, which are logical variables (of
 * the appropriate types). From here on we'll shift to stating logical properties
 * as ensures clauses of lemmas, the typical way they'd be packaged in Dafny. */
lemma AdditionCommutes(n: int, m: int)
  ensures n + m == m + n
{
  // The proof of this lemma goes here. In this case (and in many others), no
  // additional assistance is needed so an empty proof suffices.
  //
  // In Dafny, we won't talk much about proofs on their own - in a course on
  // logic you might go over logical rules or proof trees - because Dafny is
  // going to have all the power you need to prove things (as long as they're true!).
}

/* Let's start by going over the simplest logical connectives: && ("and") and ||
 * ("or"). In these examples think of the input booleans as being arbitrary
 * predicates, except that by the time we've passed them to these lemmas their
 * represented as just a truth value. */

lemma ProveAndFromBoth(p1: bool, p2: bool)
  requires p1
  requires p2
  ensures p1 && p2
{}

lemma FromAndProveRight(p1: bool, p2: bool)
  requires p1 && p2
  ensures p2
{}

lemma ProveOrFromLeft(p1: bool, p2: bool)
  requires p1
  ensures p1 || p2
{}

/* Let's also see _negation_ written `!p`, boolean negation. Asserting or
 * ensuring `!p` is the way we prove it's false. */
lemma DoubleNegation(p: bool)
  requires p
  ensures !!p
{}

lemma LawOfExcludedMiddle(p: bool)
  ensures p || !p
{}

/* Now we'll introduce boolean implication, `p ==> q`, read as "if p, then q". In "p
 * ==> q" we'll sometimes refer to "p" as a hypothesis and "q" as a conclusion.
 * Here are some alternative English logical
 * statements and how they map to implication:
 *
 * "p if q" means "q ==> p"
 * "p only if q" means "p ==> q" (this one can be tricky!)
 * "p implies q" means "p ==> q"
 */

/* Note that p ==> q is itself a proposition! Here's its "truth table", showing
 * all possible combinations of p and q and whether p ==> q is true: */
lemma ImplicationTruthTable()
  ensures false ==> false
  ensures false ==> true
  ensures !(true ==> false)
  ensures false ==> true
{}

/* One of the most famous rules of logic, which allows us to take an implication
 * (already proven correct) and a proof of its hypothesis to derive its
 * conclusion.
 *
 * Note that both parts are important! We can prove `false ==> 2 < 1` but will
 * never be able to use ModusPonens on this to prove `2 < 1`. Well we could, but
 * since this is obviously false it would mean we accidentally assumed false
 * somewhere else - this is also called an _inconsistency_.
 */
lemma ModusPonens(p1: bool, p2: bool)
  requires p1 ==> p2
  requires p1
  ensures p2
{}

/* We can write a lemma above as implications in ensures clauses, rather than
 * using preconditions. The key difference is that calling `FromAndProveLeft(p1,
 * p2)` for example will cause Dafny to immediately prove `p1 && p2`, whereas we
 * can always call `AndProvesBoth(p1, p2)` and Dafny won't check anything
 * (because the implications are true regardless of p1 and p2). */
lemma AndProvesBoth(p1: bool, p2: bool)
  ensures p1 && p2 ==> p1
  ensures p1 && p2 ==> p2
{}

/* Let's introduce one more logical connective: `p <==> q`, "p if and only if q"
 * (also written "iff" and pronounced "if and only if"). This has the same truth
 * value as `p == q`. The whole thing is sometimes called a "biconditional".
 * This rule is a little like modus ponens but requiring the implication is
 * stronger than needed. */
lemma ProveFromBiconditional(p1: bool, p2: bool)
  requires p1
  requires p1 <==> p2
  ensures p2
{}

/* Simplifying and comprehending logical expressions is something you'll
 * gradually get practice with. It can get quite complicated! */
lemma SomeEquivalences(p1: bool, p2: bool)
  ensures ((p1 ==> p2) && p1) ==> p2
  ensures !(p1 ==> !p2) <==> p1 && p2
  ensures ((p1 ==> p2) && (!p1 ==> p2)) <==> p2
  // you might want to think about this one:
  ensures (!p1 || (p1 ==> p2)) <==> (p1 ==> p2)
{}

lemma SomeMoreEquivalences(p1: bool, p2: bool, p3: bool)
  // note on parsing: <==> has the lowest priority, so all of these statements are
  // equivalences at the top level
  ensures (p1 && p2) && p3 <==> p1 && p2 && p3
  // this is what chained implications mean
  ensures p1 ==> p2 ==> p3 <==> p1 && p2 ==> p3
  ensures p1 ==> (p2 ==> p3) <==> p1 && p2 ==> p3
{}
