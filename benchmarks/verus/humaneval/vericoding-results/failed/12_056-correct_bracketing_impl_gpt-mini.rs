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
/* helper modified by LLM (iteration 5): map a bracket char to its integer delta */
spec fn char_delta(c: char) -> int { if c == '<' { 1 } else if c == '>' { -1 } else { 0 } }
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
    /* code modified by LLM (iteration 5): iterate over sequence using char_delta and maintain depth and ok with invariants relating to prefix sums */
    let seq = brackets@;
    let mut i: nat = 0;
    let mut depth: int = 0;
    let mut ok: bool = true;
    while i < seq.len()
        invariant
            depth == seq[..i].fold_left(0, |x: int, c: char| x + char_delta(c)),
            ok == (forall |j: nat| j < i ==> seq[..j+1].fold_left(0, |x: int, c: char| x + char_delta(c)) >= 0),
        decreases seq.len() - i
    {
        let c = seq@[i];
        let nd = depth + char_delta(c);
        depth = nd;
        if nd < 0 {
            ok = false;
        }
        i = i + 1;
    }
    ok && depth == 0
}
// </vc-code>

}
fn main() {}