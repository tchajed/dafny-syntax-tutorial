datatype Interval = Interval(lo: real, hi: real)

function contains(i: Interval, r: real): bool {
  i.lo <= r <= i.hi
}

function empty(i: Interval): bool {
  i.lo > i.hi
}

lemma empty_ok(i: Interval)
  ensures empty(i) <==> !exists r :: contains(i, r)
{
  if !empty(i) {
    assert contains(i, i.lo);
  }
}
