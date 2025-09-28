// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_palindrome(s: Seq<int>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i]
}

spec fn sum_elements(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_elements(s.subrange(1, s.len() as int))
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers provided */
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting */
{
    let ghost_s_int = q@.map(|_i: int, x: i8| x.into());

    let palindrome_check = is_palindrome(ghost_s_int);
    let sum_check = sum_elements(ghost_s_int) <= w.into();

    palindrome_check && sum_check
}
// </vc-code>


}

fn main() {}