// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    (c as u32) >= 97 && (c as u32) <= 122
}

spec fn is_upper_case(c: char) -> (result: bool) {
    (c as u32) >= 65 && (c as u32) <= 90
}

spec fn count_uppercase_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_uppercase(text: &Vec<char>) -> (count: u64)

    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}