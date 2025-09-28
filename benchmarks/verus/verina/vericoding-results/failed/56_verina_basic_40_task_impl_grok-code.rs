// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn second_smallest_precond(s: &Vec<i32>) -> bool {
    s.len() > 1
}

spec fn second_smallest_postcond(s: &Vec<i32>, result: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == result) &&
    (exists|j: int| 0 <= j < s.len() && s[j] < result &&
        (forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type errors by using correct initialization for min and second smallest, avoiding usize in assertions */
{
    let mut min_val: i32 = i32::MAX;
    let mut j: usize = 0;
    for i in 0..s.len() {
        if s[i] < min_val {
            min_val = s[i];
            j = i;
        }
    }
    let mut second_val: i32 = i32::MAX;
    for i in 0..s.len() {
        if s[i] != min_val && s[i] < second_val {
            second_val = s[i];
        }
    }
    let result = second_val;
    result
}
// </vc-code>

}
fn main() {}