use vstd::prelude::*;

verus! {

// Interval is the Verus model of the data structure itself. We're using `real`
// here for the numbers; the specifics don't really matter, as long as we can
// compare them with <.
pub enum Interval {
    Interval { lo: real, hi: real }
}

// Contains is one of the core operations on intervals, both because we support
// it in the API and because in some ways it defines what the interval means.
pub open spec fn contains(i: Interval, r: real) -> bool {
    i.lo <= r <= i.hi
}

// We also provide a way to check if an interval is empty.
pub open spec fn empty(i: Interval) -> bool {
    i.lo > i.hi
}

// Empty is a way to check if an interval doesn't contain any numbers - let's prove that empty and contains agree with each other.
pub proof fn empty_ok(i: Interval)
    ensures empty(i) <==> !exists|r: real| contains(i, r)
{
}

// min and max are just helper functions for the implementation
pub open spec fn min(r1: real, r2: real) -> real {
    if r1 < r2 { r1 } else { r2 }
}

pub open spec fn max(r1: real, r2: real) -> real {
    if r1 > r2 { r1 } else { r2 }
}

// The first complicated operation we expose is a function to intersect two intervals.
pub open spec fn intersect(i1: Interval, i2: Interval) -> Interval {
    Interval { lo: max(i1.lo, i2.lo), hi: min(i1.hi, i2.hi) }
}

// This theorem proves that intersect does exactly what we wanted it to, using `contains` as the specification.
pub proof fn intersect_ok(i1: Interval, i2: Interval)
    ensures forall|r: real| contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

// Intersect gives us an easy way to define overlap, and we already know it handles empty intervals correctly.
pub open spec fn overlap(i1: Interval, i2: Interval) -> bool {
    !empty(intersect(i1, i2))
}

pub proof fn overlap_ok(i1: Interval, i2: Interval)
    ensures overlap(i1, i2) <==> exists|r: real| contains(i1, r) && contains(i2, r)
{
}

// We'll give this function a precondition so that it always does the right thing.
pub open spec fn union(i1: Interval, i2: Interval) -> Interval
    recommends overlap(i1, i2)
{
    Interval { lo: min(i1.lo, i2.lo), hi: max(i1.hi, i2.hi) }
}

// We can prove union correct in much the same way as intersect, with a similar specification.
pub proof fn union_ok(i1: Interval, i2: Interval)
    requires overlap(i1, i2)
    ensures forall|r: real| contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
{
}

// This lemma returns a value which is used in the postcondition.
pub proof fn overlap_witness(i1: Interval, i2: Interval) -> (r: real)
    requires overlap(i1, i2)
    ensures contains(i1, r) && contains(i2, r)
{
    if i1.lo >= i2.lo {
        i1.lo
    } else {
        i2.lo
    }
}

}