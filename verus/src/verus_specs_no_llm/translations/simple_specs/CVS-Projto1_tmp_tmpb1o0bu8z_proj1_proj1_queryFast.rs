// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>, a
{
  a.Length + 1 == c.Length
  && c[0] == 0
  && forall j: : 1 <= j <= a.Length ==> c[j] == sum(a, 0, j)
}


// SPEC

method queryFast (a: Vec<int>, c: Vec<int>, i: int, j: int) returns (r:int)
requires is_prefix_sum_for(a, c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i, j) -> bool {
    
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