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
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}


// SPEC


method queryFast(a: array<int>, c: Vec<int>, i: int, j: int) returns (r: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c) 
  ensures r == sum(a, i, j) -> bool {
    
}

fn queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        a.len() + 1 == c.len() && c.spec_index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a,c)
    ensures
        r == sum(a, i, j)
{
    return 0;
}

}