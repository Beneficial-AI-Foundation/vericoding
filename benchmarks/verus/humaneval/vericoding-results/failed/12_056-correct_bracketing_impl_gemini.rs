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
/* helper modified by LLM (iteration 5): retained helper as it is required to prove the loop invariant. */
proof fn lemma_spec_bracketing_helper_unfold(brackets: Seq<char>)
    requires
        brackets.len() > 0,
    ensures
        spec_bracketing_helper(brackets) == {
            let sub = brackets.subrange(0, (brackets.len() - 1) as int);
            let last = brackets@[brackets.len() - 1];
            let p_init = spec_bracketing_helper(sub);
            let (x, b) = p_init;
            match (last) {
                '<' => (x + 1, b),
                '>' => (x - 1, b && x - 1 >= 0),
                _ => (x, b),
            }
        },
{
}

/* helper modified by LLM (iteration 5): retained helper as it is required to prove the loop invariant. */
proof fn lemma_spec_bracketing_helper_bounds(brackets: Seq<char>)
    ensures
        -(brackets.len() as int) <= spec_bracketing_helper(brackets).0,
        spec_bracketing_helper(brackets).0 <= brackets.len() as int,
    decreases brackets.len()
{
    if brackets.len() > 0 {
        let sub = brackets.subrange(0, (brackets.len() - 1) as int);
        lemma_spec_bracketing_helper_bounds(sub);
        lemma_spec_bracketing_helper_unfold(brackets);
    }
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
    /* code modified by LLM (iteration 5): fixed compilation errors by using executable types (usize, i32) for loop variables and logic. */
    let s_ghost = brackets@;

    let mut count: i32 = 0;
    let mut valid: bool = true;

    let mut i: usize = 0;
    while i < brackets.len()
        invariant
            s_ghost === brackets@,
            0 <= i <= brackets.len(),
            (count as int, valid) == spec_bracketing_helper(s_ghost.subrange(0, i as int)),
        decreases brackets.len() - i
    {
        let c = brackets.as_bytes()[i] as char;

        proof {
            let next_sub = s_ghost.subrange(0, (i + 1) as int);
            lemma_spec_bracketing_helper_unfold(next_sub);
            assert(s_ghost[i as int] == c);
        }

        if c == '<' {
            count = count + 1;
        } else if c == '>' {
            let new_count = count - 1;
            valid = valid && (new_count >= 0);
            count = new_count;
        }

        i = i + 1;
    }

    return valid && (count == 0);
}
// </vc-code>

}
fn main() {}