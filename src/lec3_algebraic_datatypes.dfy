/* More interesting data to reason about: algebraic datatypes. */

/*** Algebraic datatypes ***/

/* Sequences are powerful and all, but eventually you'll want to define new data
 * types. For that Dafny has algebraic datatypes which capture "products"
 * (struct-like types) and "sums" (tagged unions). These are often abbreviated to
 * "ADTs" (not to be confused with "abstract data types" which are a totally
 * different concept related to object-oriented programming; we won't generally
 * use that term). Algebraic datatypes are also used for programming (as opposed
 * to in the course where we'll only see them used for mathematical models), so
 * we'll take a short break and first explain them in the context of functions
 * before seeing them used in lemmas and assertions. */

/*** Structs (products) ***/

// {{{

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

// }}}

/*** Variants (sums) ***/

// {{{

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

/* More functions on data types */

datatype DnaBase = Cytosine | Guanine | Adenine | Thymine

function PairedBase(b: DnaBase): DnaBase {
  match b {
    case Cytosine => Guanine
    case Guanine => Cytosine
    case Adenine => Thymine
    case Thymine => Adenine
    /* This list is exhaustive, which is checked by Dafny.
     *
     * If we discovered a new base and added it to the list, this would guide us
     * in updating all of our code. However, it would be not be so easy to
     * update our understand of genetics in that case.
     */
  }
}

// New feature (type synonym): a type synonym is simply a shorthand for an existing type
type Strand = seq<DnaBase>

// can these two strands be paired in one DNA molecule?
predicate PairedStrands(s1: Strand, s2: Strand) {
  // New feature: Dafny has a prefix-and syntax (borrowed from TLA+). This is
  // really convenient for writing a list of conjuncts in a symmetric way where
  // they can be re-ordered or added/removed.
  && |s1| == |s2|
     // precondition checking is still at work here! the first conjunct is needed
     // to guarantee that `s2[i]` is in-bounds here
  && forall i | 0 <= i < |s1| :: s2[i] == PairedBase(s1[i])
}

// }}}

/*** Combining structs and variants ***/

// {{{

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
//
// (If you don't know much about coffee, that's okay! Take this as a
// specification for what these drinks are, at least as far as milk is
// concerned.)
function MilkOz(coffee: CoffeeRecipe): nat {
  match coffee {
    // New feature (ignore patterns): we can put an underscore for fields that
    // aren't needed in some "match arm". We can also name a field and refer to
    // it on the right side (notice that this name also doesn't have to match
    // the name in the datatype).
    case Drip(_, milk) => if milk then 1 else 0
    case Espresso(_) => 0
    // standard-sized latte
    case Latte(_) => 8
  }
}

// }}}

/*** Algebraic datatypes in lemmas and assertions ***/

// {{{

lemma VariantsDiffer() {
  assert Sunday != Monday;
}

predicate MilkDrink(coffee: CoffeeRecipe) {
  match coffee {
    case Latte(_) => true
    // this is intentionally wrong to illustrate something
    case _ => false
  }
}

lemma MilkDrink_spec_v1(coffee: CoffeeRecipe)
  ensures MilkDrink(coffee) <==> (MilkOz(coffee) > 0)
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
  ensures MilkDrink(coffee) <==> (MilkOz(coffee) > 0)
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

/* Discriminators and fields of variants */

/* In addition to match statements, Dafny has another way to check which variant
 * a datatype was constructed with and to access fields of datatypes with
 * multiple variants. */

// we'll use these features to make another attempt at this theorem with an
// appropriate precondition
lemma MilkDrink_spec_alt(coffee: CoffeeRecipe)
  requires
    // New feature (discriminator): coffee.Drip? is a predicate that is true if
    // coffee was constructed with the Drip(...) variant. It's automatically
    // defined by Dafny.
    coffee.Drip? ==>
      // New feature (fields of variant datatypes): Dafny allows accessing a field
      // of a particular variant even when there are multiple variants. This field
      // access has an implicit precondition `coffee.Drip?` - just like for
      // accessing sequences, all uses (including in specifications) need to
      // guarantee this precondition, which in this case comes from the
      // `coffee.Drip? ==>`.
      !coffee.room_for_milk
  ensures MilkDrink(coffee) <==> (MilkOz(coffee) > 0)
{
  // We can use both of these new features in the proof instead of a match
  // statement, which might be more convenient or natural in some cases
  // (especially when building a proof incrementally it can allow checking
  // particular cases without writing out the match statement).
  if coffee.Latte? {
    var typ := coffee.milk_type;
  } else if coffee.Drip? {
    assert !coffee.room_for_milk;
  } else if coffee.Espresso? {}

  // (the proof in this is unnecessary because the lemma is simple enough)
}

// }}}
