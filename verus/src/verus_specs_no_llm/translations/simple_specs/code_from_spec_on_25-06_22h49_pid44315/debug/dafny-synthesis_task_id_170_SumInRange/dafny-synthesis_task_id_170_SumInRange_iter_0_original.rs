// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumInRange(a: Vec<int>, start: int, end: int) -> (sum: int)
    requires
        a != null,
        0 <= start && start <= end && end <= a.len()
    ensures
        sum == sumTo(a, start, end)
{
    return 0;
}

}