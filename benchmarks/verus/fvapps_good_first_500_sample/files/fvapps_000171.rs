// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn contains_dot(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == '.'
}

spec fn contains_newline(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == '\n'
}

fn length_longest_path(input: &str) -> (result: usize)
    ensures 
        input@.len() == 0 ==> result == 0,
        (input@.len() > 0 && contains_dot(input@) && !contains_newline(input@)) ==> result == input@.len(),
        (input@.len() > 0 && !contains_dot(input@) && !contains_newline(input@)) ==> result == 0
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

    // Test cases:
    // length_longest_path("dir\n\tsubdir1\n\tsubdir2\n\t\tfile.ext") should return 20
    // length_longest_path("dir\n\tsubdir1\n\t\tfile1.ext\n\t\tsubsubdir1\n\tsubdir2\n\t\tsubsubdir2\n\t\t\tfile2.ext") should return 32
    // length_longest_path("") should return 0
}