// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_digit(c: char) -> bool {
    c >= '0' && c <= '9'
}
// </vc-helpers>

// <vc-spec>
fn all_digits(s: &str) -> (result: bool)
    requires true,
    ensures
        result == (forall|i: int| 0 <= i < s.unicode_len() ==> is_digit(s.get_char(i))),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}

proof fn all_digits_spec_satisfied(s: &str)
    ensures all_digits(s) == (forall|i: int| 0 <= i < s.unicode_len() ==> is_digit(s.get_char(i)))
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}
fn main() {}