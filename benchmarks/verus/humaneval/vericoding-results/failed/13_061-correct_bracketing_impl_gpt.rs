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
/* helper modified by LLM (iteration 5): simplified bracket predicates and state update with a small monotonicity lemma */
spec fn is_open(c: char) -> bool { c == '(' }
spec fn is_close(c: char) -> bool { c == ')' }
spec fn step_state(x: (int, bool), c: char) -> (int, bool) { let (n, ok) = x; if is_open(c) { (n + 1, ok) } else if is_close(c) { (n - 1, ok && n - 1 >= 0) } else { (n, ok) } }
proof fn step_state_monotonic_ok(x: (int, bool), c: char)
    ensures
        step_state(x, c).1 ==> x.1,
{ }
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
{
    /* code modified by LLM (iteration 5): iterate over characters using chars() to avoid as_bytes; straightforward counting */
    let mut count: i32 = 0;
    let mut ok: bool = true;
    for c in brackets.chars() {
        if c == '(' {
            count = count + 1;
        } else if c == ')' {
            if count == 0 {
                ok = false;
            } else {
                count = count - 1;
            }
        }
    }
    ok && count == 0
}
// </vc-code>

}
fn main() {}