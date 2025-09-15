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
/* helper modified by LLM (iteration 5): fixed ensures clause syntax */
fn find_min_value(s: &Vec<i32>) -> (min_val: i32)
    requires s.len() > 0
    ensures exists|j: int| 0 <= j < s.len() && s[j] == min_val
    ensures forall|k: int| 0 <= k < s.len() ==> s[k] >= min_val
{
    let mut min_val = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            0 < i <= s.len(),
            exists|j: int| 0 <= j < s.len() && s[j] == min_val,
            forall|k: int| 0 <= k < i ==> s[k] >= min_val
    {
        if s[i] < min_val {
            min_val = s[i];
        }
        i = i + 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed function implementation */
    let min_val = find_min_value(s);
    
    let mut second_min = i32::MAX;
    let mut found_second = false;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            found_second ==> (exists|j: int| 0 <= j < s.len() && s[j] == second_min),
            found_second ==> second_min != min_val,
            found_second ==> (forall|k: int| 0 <= k < i && s[k] != min_val ==> s[k] >= second_min)
    {
        if s[i] != min_val {
            if !found_second || s[i] < second_min {
                second_min = s[i];
                found_second = true;
            }
        }
        i = i + 1;
    }
    
    second_min
}
// </vc-code>

}
fn main() {}