datatype Interval = Interval(lo: real, hi: real)

predicate empty(i: Interval) {
  i.lo > i.hi
}

predicate contains(i: Interval, r: real) {
  i.lo <= r <= i.hi
}

function min(r1: real, r2: real): real {
  if r1 < r2 then r1 else r2
}

function max(r1: real, r2: real): real {
  if r1 > r2 then r1 else r2
}

datatype Option<T> = Some(v: T) | None

predicate overlap(i1: Interval, i2: Interval) {
  !empty(i1) && !empty(i2) &&
    // this would make them disjoint
  !(i1.hi < i2.lo || i2.hi < i1.lo)
}

function union(i1: Interval, i2: Interval): Option<Interval> {
  if overlap(i1, i2) then
    Some(Interval(min(i1.lo, i2.lo), max(i1.hi, i2.hi)))
  else
    None
}

function intersect(i1: Interval, i2: Interval): Interval {
  Interval(max(i1.lo, i2.lo), min(i1.hi, i2.hi))
}

lemma empty_ok(i: Interval)
  ensures empty(i) <==> !exists r :: contains(i, r)
{
  if empty(i) {
  } else {
    assert contains(i, i.lo);
  }
}

lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
{
  if i1.lo >= i2.lo {
    r := i1.lo;
  } else {
    r := i2.lo;
  }
}

lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r :: contains(union(i1, i2).v, r) <==> contains(i1, r) || contains(i2, r)
{
}

lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

// this would have been a simpler way to define overlap
predicate overlap2(i1: Interval, i2: Interval) {
  !empty(intersect(i1, i2))
}

lemma overlap2_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) == overlap2(i1, i2)
{}
