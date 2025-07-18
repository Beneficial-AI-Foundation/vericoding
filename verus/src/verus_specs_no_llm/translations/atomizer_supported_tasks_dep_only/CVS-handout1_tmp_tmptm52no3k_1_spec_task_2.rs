// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}


// ATOM 

lemma aux(a: array<int>, c: Vec<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures forall k: int :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k] //sum(a, i, j) == c[j] - c[i]
{}



// SPEC 


method queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a, c)  
    ensures r == sum(a, i, j) -> bool {
    
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
    reads a
    requires
        0 <= i <= j <= a.len()
{
    0
}

spec fn spec_queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> r: int
    requires
        a.len() + 1 == c.len() && c.index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a,c)
    ensures
        r == sum(a, i, j)
;

proof fn lemma_queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        a.len() + 1 == c.len() && c.index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a,c)
    ensures
        r == sum(a, i, j)
{
    0
}

}