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
/* helper modified by LLM (iteration 5): added lemma to prove postcondition from loop invariants */
proof fn lemma_second_smallest_correct(s: &Vec<i32>, min_val: i32, second_val: i32)
    requires
        s.len() > 1,
        (exists|i: int| 0 <= i < s.len() && s[i] == min_val),
        (forall|j: int| 0 <= j < s.len() ==> s[j] >= min_val),
        (exists|i: int| 0 <= i < s.len() && s[i] == second_val),
        second_val > min_val,
        (forall|j: int| 0 <= j < s.len() && s[j] != min_val ==> s[j] >= second_val)
    ensures second_smallest_postcond(s, second_val)
{
    // The postcondition requires:
    // 1. second_val exists in s (satisfied by precondition)
    // 2. There exists some value < second_val with property that all other values >= second_val
    // This is satisfied by min_val being < second_val and our invariants
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants and added proof for postcondition */
    let mut min_val = s[0];
    let mut idx: usize = 1;
    
    while idx < s.len()
        invariant
            1 <= idx <= s.len(),
            (exists|i: int| 0 <= i < s.len() && s[i] == min_val),
            (forall|j: int| 0 <= j < idx ==> s[j] >= min_val)
        decreases s.len() - idx
    {
        if s[idx] < min_val {
            min_val = s[idx];
        }
        idx += 1;
    }
    
    let mut second_val = i32::MAX;
    let mut found = false;
    idx = 0;
    
    while idx < s.len()
        invariant
            0 <= idx <= s.len(),
            (forall|j: int| 0 <= j < s.len() ==> s[j] >= min_val),
            found ==> (exists|i: int| 0 <= i < s.len() && s[i] == second_val),
            found ==> second_val > min_val,
            found ==> (forall|j: int| 0 <= j < idx && s[j] != min_val ==> s[j] >= second_val),
            !found ==> (forall|j: int| 0 <= j < idx ==> s[j] == min_val)
        decreases s.len() - idx
    {
        if s[idx] != min_val {
            if !found || s[idx] < second_val {
                second_val = s[idx];
                found = true;
            }
        }
        idx += 1;
    }
    
    proof {
        lemma_second_smallest_correct(s, min_val, second_val);
    }
    
    second_val
}
// </vc-code>

}
fn main() {}