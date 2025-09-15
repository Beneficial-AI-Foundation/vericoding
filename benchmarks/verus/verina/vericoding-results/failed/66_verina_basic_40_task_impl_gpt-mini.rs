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
/* helper modified by LLM (iteration 5): spec function for minimal element */
spec fn min_vec(s: &Vec<i32>) -> i32 {
    choose|m: i32| (exists|i: int| 0 <= i && i < s.len() && s@[i] == m) && (forall|j: int| 0 <= j && j < s.len() ==> s@[j] >= m)
}

/* helper modified by LLM (iteration 5): spec function for minimal element excluding a value */
spec fn min_excluding(s: &Vec<i32>, excl: i32) -> i32 {
    choose|m: i32| (exists|i: int| 0 <= i && i < s.len() && s@[i] == m && s@[i] != excl) && (forall|j: int| 0 <= j && j < s.len() && s@[j] != excl ==> s@[j] >= m)
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute smallest and second-smallest with scans */
    let mut min1: i32 = s[0];
    let mut i: usize = 1;
    while i < s.len() {
        if s[i] < min1 { min1 = s[i]; }
        i += 1;
    }
    // find first index not equal to min1
    let mut j: usize = 0;
    while j < s.len() && s[j] == min1 {
        j += 1;
    }
    if j == s.len() {
        // all elements equal: return min1
        min1
    } else {
        let mut min2: i32 = s[j];
        let mut k: usize = j + 1;
        while k < s.len() {
            if s[k] != min1 && s[k] < min2 { min2 = s[k]; }
            k += 1;
        }
        min2
    }
}
// </vc-code>

}
fn main() {}