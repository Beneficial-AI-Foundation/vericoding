// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>, a
{
 a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}


// SPEC

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) returns (r: int)
 requires 0 <= i <= j <= a.Length
 requires is_prefix_sum_for(a, c)
 ensures r == sum(a, i, j) -> bool {
    
}

fn queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a,c)
    ensures
        r == sum(a, i, j)
{
    return 0;
}

}