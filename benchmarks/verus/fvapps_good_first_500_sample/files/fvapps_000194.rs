// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn equal_substring(s: Vec<char>, t: Vec<char>, max_cost: u32) -> (result: u32)
    requires s.len() == t.len(),
    ensures
        result <= s.len(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // println!("{}", equal_substring("abcd", "bcdf", 3)); // Should output 3
    // println!("{}", equal_substring("abcd", "cdef", 3)); // Should output 1  
    // println!("{}", equal_substring("abcd", "acde", 0)); // Should output 1
}