// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_digit_sepc(c: char) -> (res: bool) {
    (c as u32) >= 48 && (c as u32) <= 57
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): exec digit checker aligned with spec predicate */
fn is_digit_exec(c: char) -> (res: bool)
    ensures
        res == is_digit_sepc(c)
{
    let v: u32 = c as u32;
    v >= 48 && v <= 57
}
/* helper modified by LLM (iteration 3): spec predicate expressing that all characters are digits */
spec fn all_digits(text: &Vec<char>) -> bool { forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i])) }
// </vc-helpers>

// <vc-spec>
fn is_integer(text: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate through characters using exec helper and maintain quantified invariant */
    let mut k: usize = 0;
    let mut res: bool = true;
    while k < text.len()
        invariant
            k <= text.len(),
            0 <= k as int <= text.len() as int,
            res == (forall|j: int| 0 <= j < k as int ==> (#[trigger] is_digit_sepc(text[j]))),
        decreases text.len() - k
    {
        let c = text[k];
        let d = is_digit_exec(c);
        proof {
            assert(d == is_digit_sepc(c));
        }
        res = res && d;
        k = k + 1;
    }
    assert(k == text.len());
    res
}
// </vc-code>

}
fn main() {}