// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (result:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type errors by using int for count and proper sequence indexing */
fn bracketing_helper(brackets: Seq<char>) -> (int, bool) {
    let mut count: int = 0;
    let mut valid = true;
    let mut i: nat = 0;
    while i < brackets.len()
        invariant
            i <= brackets.len(),
        decreases brackets.len() - i,
    {
        match brackets@[i] {
            '<' => { count = count + 1; },
            '>' => {
                count = count - 1;
                if count < 0 {
                    valid = false;
                }
            },
            _ => (),
        }
        i = i + 1;
    }
    (count, valid && count == 0)
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
/* code modified by LLM (iteration 5): updated to use the fixed helper function with correct types */
{
    let (count, valid) = bracketing_helper(brackets@);
    valid
}
// </vc-code>

}
fn main() {}