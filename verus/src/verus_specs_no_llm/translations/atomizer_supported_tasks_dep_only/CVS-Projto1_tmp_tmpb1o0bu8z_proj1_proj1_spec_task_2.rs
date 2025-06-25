// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        is_prefix_sum_for(a,c) && 0 <= i <= j <= a.len() < c.len()
    ensures
        r == sum(a, i,j)
{
    return 0;
}

}