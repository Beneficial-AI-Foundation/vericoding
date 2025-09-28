// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used nat for loop counter and restructured if to fix type errors */
fn is_integer_impl(s: Seq<char>) -> (result: bool)
    ensures result <==> ((s.len() > 0) && forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
{
    if s.len() > 0 {
        let mut i: nat = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                s.len() > 0,
                forall|j: int| 0 <= j < i as int ==> is_digit(s[j]),
            decreases s.len() - i
        {
            if !is_digit(s@[i]) {
                return false;
            }
            i = i + 1;
        }
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): maintaining call to fixed helper function */
    is_integer_impl(s)
}
// </vc-code>

}
fn main() {}