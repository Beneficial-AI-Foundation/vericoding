// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}