// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j { 
        0 
    } else { 
        a[i] + sum(a, i + 1, j) 
    }
}

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    &&& a.len() + 1 == c.len() 
    &&& c.len() > 0 
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn queryFast(a: &Vec<i8>, c: &Vec<i8>, i: i8, j: i8) -> (r: i8)
    requires a@.len() + 1 == c@.len() && c@.len() > 0 && c@[0] as int == 0,
        0 <= i as int <= j as int <= a@.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}