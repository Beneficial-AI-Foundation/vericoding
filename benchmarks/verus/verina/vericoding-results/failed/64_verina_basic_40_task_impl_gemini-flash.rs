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
/* helper modified by LLM (iteration 5): Adding a helper function to determine if a value is the second smallest in a sequence up to a given index. */
spec fn is_second_smallest_in_prefix(s: &Vec<i32>, val: i32, len: int) -> bool {
    (exists|i: int| 0 <= i < len && s[i] == val) &&
    (exists|j: int| 0 <= j < len && s[j] < val &&
        (forall|k: int| 0 <= k < len && s[k] != s[j] ==> s[k] >= val))
}

spec fn is_smallest_in_prefix(s: &Vec<i32>, val: i32, len: int) -> bool {
    (exists|i: int| 0 <= i < len && s[i] == val) &&
    (forall|k: int| 0 <= k < len ==> s[k] >= val)
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected the loop invariant for `smallest` and `second_smallest_val` to accurately reflect their definitions based on the prefix of the sequence. Also, refined the logic within the loop body to correctly update `smallest` and `second_smallest_val` to maintain these invariants, and adjusted the initial assignment when `s[0] == s[1]` to correctly initialize `second_smallest_val`. */
{
    let mut smallest: i32;
    let mut second_smallest_val: i32;

    if s[0] < s[1] {
        smallest = s[0];
        second_smallest_val = s[1];
    } else if s[0] > s[1] {
        smallest = s[1];
        second_smallest_val = s[0];
    } else { // s[0] == s[1]
        smallest = s[0];
        second_smallest_val = s[0]; // will be updated if a larger value is found later
    }

    let mut i = 2;

    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            is_smallest_in_prefix(s, smallest, i),
            is_second_smallest_in_prefix(s, second_smallest_val, i),
            smallest <= second_smallest_val
        decreases s.len() - i
    {
        if s[i] < smallest {
            second_smallest_val = smallest;
            smallest = s[i];
        } else if s[i] < second_smallest_val && s[i] > smallest {
            second_smallest_val = s[i];
        } else if smallest == second_smallest_val && s[i] > smallest {
            second_smallest_val = s[i];
        }
        i = i + 1;
    }
    second_smallest_val
}
// </vc-code>

}
fn main() {}