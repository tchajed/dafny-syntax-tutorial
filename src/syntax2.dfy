/* More interesting data to reason about */

/* Outline:
- sequences
- algebraic data types (user-defined data)
*/

/* In order to write proofs about interesting systems and protocols, we first
need some way of modeling the state of those systems and protocols. We'll
explore Dafy's built-in sequence type as well as algebraic data types, its core
way of creating user-defined types.

/*** Sequences ***/

These data types are very similar to data structures, but will be purely
mathematical. We'll start with the sequence type `seq<T>`. The `T` in angle
brackets is a _type parameter_, needed because sequences can hold values of any
type. A sequence is related to data structures you're familiar with like linked
lists or arrays/vectors (the terminology depends on the programming language). A
sequence is the mathematical essence of the state of a list/vector/array without
the implementation details.
*/

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
  requires SeqGet(s, i) > 0 // error: function precondition might not hold
{}

lemma SequenceAppendFact(s1: seq<int>, s2: seq<int>)
  // New syntax (forall where conditions): notice the new pipe symbol after the `i`. The
  // general syntax is of the form `forall x | p(x) :: q(x)`; it means the same //
  // thing as `forall x :: p(x) ==> q(x)` but can be easier to read. You might read this
  // as "for all x where p(x), q(x)".
  //
  // We're also leaving off the type of `i` because Dafny can infer that it's an `int`.
  ensures forall i | |s1| <= i < |s1| + |s2| :: (s1 + s2)[i] == s2[i - |s1|]
{
  // goes through without any extra proof
}


/*** Algebraic data types ***/

/* Sequences are powerful and all, but eventually you'll want to define new data
types. For that Dafny has algebraic data types which capture "products"
(struct-like types) and "sums" (tagged unions). While we're explaining algebraic
data types we'll take a short break from lemmas/proofs and just explain this bit
of functional programming. */

/* Let's start with a struct that has two fields, x and y: */
datatype Point = PointCtor(x: int, y: int)

/* We've called the type `Point` and its constructor `PointCtor`. It's common
and allowed to give these the same name, since Dafny can distinguish whether we
want the type or the function from context:

   datatype Point = Point(x: int, y: int)
 */

function SquaredDistance(p: Point): int {
  // the main thing we do with a struct is to get its fields
  p.x * p.x + p.y * p.y
}

// Here's an example of constructing a Point:
const Origin: Point := PointCtor(0, 0);

/* Next, a datatype can have several "variants" which are mutually exclusive. In
the simplest case, this produces an enum: */
datatype DayOfWeek = Sunday | Saturday | Monday | Tuesday | Wednesday | Thursday | Friday

predicate IsWeekend(w: DayOfWeek) {
  match w {
    case Sunday => true
    case Saturday => true
    case _ => false
  }
}

datatype DnaBase = Cytosine | Guanine | Adenine | Thymine

function PairedBase(b: DnaBase): DnaBase {
  match b {
    case Cytosine => Guanine
    case Guanine => Cytosine
    case Adenine => Thymine
    case Thymine => Adenine
    // This list is exhaustive, which is checked by Dafny.
    //
    // If we discovered a new base and added it to the list, this would guide us
    // in updating all of our code. However, it would be not be so easy to
    // update our understand of genetics in that case.
  }
}

// new feature: a type synonym is simply a shorthand for an existing type
type Strand = seq<DnaBase>

// can these two strands be paired in one DNA molecule?
predicate PairedStrands(s1: Strand, s2: Strand) {
  // New feature: Dafny has a prefix-and syntax (borrowed from TLA+). This is //
  // really convenient for writing a list of conjuncts in a symmetric way where
  // they can be re-ordered or added/removed.
  && |s1| == |s2|
     // precondition checking is still at work here! the first conjunct is needed
     // to guarantee that `s2[i]` is in-bounds here
  && forall i | 0 <= i < |s1| :: s2[i] == PairedBase(s1[i])
}

/* The variants of a datatype can also have fields, combining the features of
structs and tagged unions: */

datatype MilkType =
    // fun fact: nobody actually likes skim milk
  // | Skim
  | Whole
  | Oat
  | Almond

datatype CoffeeRecipe =
  | Drip(oz: nat, room_for_milk: bool)
  | Espresso(double_shot: bool)
  | Latte(milk_type: MilkType)
    // a very incomplete list :)

// How much milk will be in my coffee drink?
function MilkOz(coffee: CoffeeRecipe): nat {
  match coffee {
    // New feature: we can put an underscore for fields that aren't needed in
    // some "match arm". We can also name a field and refer to it on the right side
    // (notice that this name also doesn't have to match the name in the datatype).
    case Drip(_, milk) => if milk then 1 else 0
    case Espresso(_) => 0
    // standard-sized latte
    case Latte(_) => 8
  }
}

/* Below we illustrate some reasoning about data types. */

lemma VariantsDiffer() {
  assert Cytosine != Guanine;
}

function MatchesExhaustive(w: DayOfWeek): DayOfWeek {
  // error says which cases we're missing (or we could have supplied a default case)
  match w {
    case Sunday => Monday
    case Monday => Tuesday
    case Tuesday => Wednesday
    case Wednesday => Thursday
    case Thursday => Friday
    // error: missing case in match expression: Saturday
    // error: missing case in match expression: Friday
  }
}

predicate MilkDrink(coffee: CoffeeRecipe) {
  match coffee {
    case Latte(_) => false
    // this is intentionally wrong to illustrate something
    case _ => true
  }
}

lemma MilkDrink_spec_v1(coffee: CoffeeRecipe)
  ensures MilkDrink(coffee) <==> (MilkOz(coffee) == 0)
{
  // Match statements are also how we do proofs involving variants
  match coffee {
    case Latte(milk) => {}
    case Espresso(drip) => {}
    case Drip(oz, milk) => { // error: A postcondition might not hold on this return path
      // the error message pinpoints this case
    }
  }
}

lemma MilkDrink_spec_v2(coffee: CoffeeRecipe)
  ensures MilkDrink(coffee) <==> (MilkOz(coffee) == 0)
{
  match coffee {
    case Latte(milk) => {}
    case Espresso(drip) => {}
    case Drip(oz, milk) => {
      if milk {
        // New feature (assume): we can put this statement in to (temporarily!)
        // ignore this case while we figure other things out. For this theorem,
        // the proof goes through except for this case, which turns out to be
        // because `MilkDrink` has a bug according to this spec.
        assume false;
      }
    }
  }
}
