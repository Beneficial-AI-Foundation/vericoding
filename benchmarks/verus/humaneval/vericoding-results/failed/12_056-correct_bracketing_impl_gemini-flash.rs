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
spec fn add_sub_sequence_axiom(s: Seq<char>, i: nat) -> Seq<char>
    recommends i <= s.len()
{
    s.subsequence(0, i)
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
{
    /* code modified by LLM (iteration 5): Fixed type of `x` to `int` and added proof for loop invariant. */
    let s_chars = brackets@;
    let (mut x, mut b) = (0, true);

    let mut i: nat = 0;
    while (i as int) < s_chars.len()
        invariant
            x >= 0, // x should not go below 0 if b is true
            b == (spec_bracketing_helper(add_sub_sequence_axiom(s_chars, i))).1,
            (i as int) <= s_chars.len(),
            0 <= (i as int),
        decreases s_chars.len() - (i as int)
    {
        proof {
            assert((spec_bracketing_helper(add_sub_sequence_axiom(s_chars, i))).1 == b);
        }
        let c = s_chars.index(i as int);
        match c {
            '<' => {
                x = x + 1;
            },
            '>' => {
                x = x - 1;
                if x < 0 {
                    b = false;
                }
            },
            _ => {},
        }

        i = i + 1;
    }

    b && x == 0
}
// </vc-code>

}
fn main() {}