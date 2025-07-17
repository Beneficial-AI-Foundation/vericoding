// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SumOfCommonDivisors(a: int, b: int) -> sum: int
    requires
        a > 0 && b > 0
    ensures
        sum >= 0,
        forall |d: int| 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
;

proof fn lemma_SumOfCommonDivisors(a: int, b: int) -> (sum: int)
    requires
        a > 0 && b > 0
    ensures
        sum >= 0,
        forall |d: int| 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
{
    0
}

}