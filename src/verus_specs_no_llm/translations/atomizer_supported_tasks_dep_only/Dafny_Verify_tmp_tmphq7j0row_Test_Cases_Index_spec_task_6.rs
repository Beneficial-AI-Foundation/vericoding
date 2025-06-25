// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ReconstructFromMaxSum(s: int, m: int) -> x: int, y: int
    requires s <= 2 * m
    ensures s == (x + y),
            (m == x or m == y) and x <= m and y <= m
{
}

}