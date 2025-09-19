// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_substring_with_k_occurrences(s: Vec<char>, k: usize) -> (result: usize)
    requires k > 0,
    ensures
        result <= s.len(),
        (s.len() == 1 && k == 1) ==> result == 1,
        (s.len() == 1 && k > 1) ==> result == 0
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

    // info: 3
    // println!("{}", longest_substring_with_k_occurrences("aaabb".chars().collect(), 3));

    // info: 5
    // println!("{}", longest_substring_with_k_occurrences("ababbc".chars().collect(), 2));

    // info: 0
    // println!("{}", longest_substring_with_k_occurrences("abcdef".chars().collect(), 2));
}