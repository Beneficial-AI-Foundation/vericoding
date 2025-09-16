// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (ret:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat usage and type issues */
fn bracketing_helper(brackets: &str) -> (i32, bool)
    ensures
        (count, valid) == spec_bracketing_helper(brackets@),
{
    let mut count = 0;
    let mut valid = true;
    let n = brackets.len();
    let mut i = 0;
    while i < n
        invariant
            (count, valid) == spec_bracketing_helper(brackets@.take(i as nat)),
            i as nat <= n,
    {
        let chars = brackets.as_bytes();
        let c = chars[i] as char;
        if c == '(' {
            count += 1;
        } else if c == ')' {
            count -= 1;
            if count < 0 {
                valid = false;
            }
        }
        i += 1;
    }
    (count, valid)
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: &str) -> (ret: bool)

    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,

    ensures
        ret <==> spec_bracketing(brackets@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using fixed bracketing_helper */
{
    let (count, valid) = bracketing_helper(brackets);
    valid && count == 0
}
// </vc-code>

}
fn main() {}