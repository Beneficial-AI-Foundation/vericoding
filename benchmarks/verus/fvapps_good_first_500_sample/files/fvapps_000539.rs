// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_digit_char(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn string_all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_digit_char(s[i])
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u32, k: u32) -> (result: (String, String))
    requires 
        n >= 2,
        k >= 1,
        n <= 1000000,
        k <= 10,
    ensures
        string_all_digits(result.0@),
        string_all_digits(result.1@),
        result.0@.len() == k,
        result.1@.len() == k,
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn string_to_nat(s: String) -> (result: u32) {
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible
}