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
/* helper modified by LLM (iteration 5): predicate to check if a char is a parenthesis */
spec fn is_paren(c: char) -> bool { c == '(' || c == ')' }
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
    /* code modified by LLM (iteration 5): iterative check over spec sequence using inferred types */
    let s = brackets@;
    let n = s.len();
    let mut i = 0;
    let mut bal = 0;
    let mut ok = true;
    while i < n
        invariant
            i <= n,
        decreases n - i
    {
        let c = s.index(i);
        if c == '(' {
            bal = bal + 1;
        } else if c == ')' {
            bal = bal - 1;
            if bal < 0 {
                ok = false;
            }
        }
        i = i + 1;
    }
    ok && bal == 0
}
// </vc-code>

}
fn main() {}