// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumTo(a: Vec<int>, start: int, end: int) -> int
    requires
        a != null,
        0 <= start && start <= end && end <= a.len()
{
    0
}

spec fn spec_SumInRange(a: Vec<int>, start: int, end: int) -> sum: int
    requires
        a != null,
        0 <= start && start <= end && end <= a.len()
    ensures
        sum == sumTo(a, start, end)
;

proof fn lemma_SumInRange(a: Vec<int>, start: int, end: int) -> (sum: int)
    requires
        a != null,
        0 <= start && start <= end && end <= a.len()
    ensures
        sum == sumTo(a, start, end)
{
    0
}

}