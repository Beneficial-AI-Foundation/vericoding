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
/* helper modified by LLM (iteration 5): Corrected type issues within the helper function by ensuring all comparisons and assignments with array elements use the correct 'i32' type. Changed loop variable 'i' to 'usize' to align with vector indexing, and cast to 'int' only for spec purposes. */
spec fn find_smallest(s: &Vec<i32>) -> (result: i32)
    requires s.len() > 0
    ensures (forall|i: int| 0 <= i < s.len() ==> s[i] >= result),
            (exists|i: int| 0 <= i < s.len() && s[i] == result)
{
    let mut smallest: i32 = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            1 <= i as int,
            i as int <= s.len() as int,
            (forall|j: int| 0 <= j < i as int ==> s[j] >= smallest),
            (exists|j: int| 0 <= j < i as int && s[j] == smallest)
        decreases s.len() - i
    {
        if s[i] < smallest {
            smallest = s[i];
        }
        i = i + 1;
    }
    smallest
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type issues within the main function by ensuring all comparisons and assignments with array elements use the correct 'i32' type. Changed loop variable 'i' to 'usize' to align with vector indexing, and cast to 'int' only for spec purposes. */
{
    let mut smallest: i32;
    let mut second_smallest: i32;

    if s[0] < s[1] {
        smallest = s[0];
        second_smallest = s[1];
    } else {
        smallest = s[1];
        second_smallest = s[0];
    }

    let mut i: usize = 2;
    while i < s.len()
        invariant
            2 <= i as int,
            i as int <= s.len() as int,
            s.len() >= 2,
            (forall|j: int| 0 <= j < i as int ==> s[j] >= smallest),
            (forall|j: int| 0 <= j < i as int && s[j] != smallest ==> s[j] >= second_smallest)
        decreases s.len() - i
    {
        if s[i] < smallest {
            second_smallest = smallest;
            smallest = s[i];
        } else if s[i] < second_smallest && s[i] != smallest {
            second_smallest = s[i];
        }
        i = i + 1;
    }
    second_smallest
}
// </vc-code>

}
fn main() {}