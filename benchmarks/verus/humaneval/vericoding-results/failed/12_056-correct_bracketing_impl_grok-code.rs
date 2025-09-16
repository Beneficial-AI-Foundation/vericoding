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
    /* code modified by LLM (iteration 5): Fixed compilation error by adjusting indexing and types, implemented runtime bracket counting with ghost proofs for spec conformity */
    let mut count = 0;
    let s = brackets@;
    let mut ghost_i: int = 0;
    let mut chars_iter = brackets.chars();
    let mut continues = true;
    while continues
        invariant
            count >= 0,
            count as int == spec_bracketing_helper(s.subrange(0, ghost_i)).0,
            spec_bracketing_helper(s.subrange(0, ghost_i)).1,
            0 <= ghost_i <= s.len() as int,
        decreases (s.len() as int) - ghost_i
    {
        if let Some(c) = chars_iter.next() {
            match c {
                '<' => count += 1,
                '>' => if count == 0 {
                    return false;
                } else {
                    count -= 1;
                },
                _ => (),
            }
            proof {
                assert(c == s@[ghost_i as int]);
                let current_s = s.subrange(0, ghost_i + 1);
                let new_p = spec_bracketing_helper(current_s);
                assert(new_p.0 == count as int);
                assert(new_p.1);
            }
            ghost_i += 1;
        } else {
            continues = false;
        }
    }
    count == 0
}
// </vc-code>

}
fn main() {}