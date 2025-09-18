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
/* helper modified by LLM (iteration 3): provide simple spec min/max helpers for clarity */
spec fn min_i32(a: i32, b: i32) -> i32 { if a < b { a } else { b } }
spec fn max_i32(a: i32, b: i32) -> i32 { if a < b { b } else { a } }
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed while-invariant syntax and ensured proper loop structure */
    let n = s.len();
    assert(n >= 2);
    let mut min_val = s[0];
    let mut second_val = s[1];
    if second_val < min_val {
        let tmp = min_val;
        min_val = second_val;
        second_val = tmp;
    }
    let mut found = second_val > min_val;
    let mut i: usize = 2;
    while i < n
        invariant
            n == s.len(),
            i <= n,
        decreases (n as int) - (i as int)
    {
        let v = s[i];
        if v < min_val {
            if found {
                second_val = min_val;
            } else {
                second_val = min_val;
                found = true;
            }
            min_val = v;
        } else if v > min_val {
            if !found || v < second_val {
                second_val = v;
                found = true;
            }
        }
        i = i + 1;
    }
    if !found {
        second_val = min_val;
    }
    second_val
}
// </vc-code>

}
fn main() {}