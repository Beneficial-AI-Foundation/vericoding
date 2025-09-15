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
/* helper modified by LLM (iteration 5): remove ghost variable for count */
spec fn count_less_than(s: &Vec<i32>, val: i32) -> nat
{
    #[spec]
    fn count_less_than_recursive(s: &Vec<i32>, val: i32, idx: nat) -> nat
        decreases s.len() - idx
    {
        if idx >= s.len() {
            0
        } else {
            let count_rest = count_less_than_recursive(s, val, idx + 1);
            if s[idx as int] < val {
                1 + count_rest
            } else {
                count_rest
            }
        }
    }
    count_less_than_recursive(s, val, 0)
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): remove `as int` cast from `s[i as int]` to fix compilation for concrete `i` */
{
    let mut smallest: i32; // Renamed 'min_val' to 'smallest' for clarity.
    let mut second_smallest_val: i32; 

    if s[0] < s[1] {
        smallest = s[0];
        second_smallest_val = s[1];
    } else {
        smallest = s[1];
        second_smallest_val = s[0];
    }

    let mut i: nat = 2;
    while i < s.len()
        invariant 
            0 <= i && i <= s.len(),
            s.len() > 1, // `precond` ensures `s.len() > 1`
            // `smallest` must be less than or equal to `second_smallest_val`
            smallest <= second_smallest_val,
            // `smallest` is the true smallest value encountered up to index `i` given initial sorting handles first two elements
            forall|k: int| 0 <= k < i ==> smallest <= s[k],
            // `second_smallest_val` is the true second smallest value encountered up to index `i` 
            //  given handling of initial two elements, excluding elements equal to `smallest`
            forall|k: int| 0 <= k < i && s[k] != smallest ==> second_smallest_val <= s[k],
            // There are at most 2 unique elements smaller than or equal to `second_smallest_val` up to `i` (smallest and second_smallest_val)
            (forall|k: int| 0 <= k < i && s[k] < second_smallest_val ==> s[k] == smallest)

    {
        let current_val: i32 = s[i];

        if current_val < smallest {
            second_smallest_val = smallest;
            smallest = current_val;
        } else if current_val < second_smallest_val && current_val != smallest {
            second_smallest_val = current_val;
        }
        i = i + 1;
    }

    second_smallest_val
}
// </vc-code>

}
fn main() {}