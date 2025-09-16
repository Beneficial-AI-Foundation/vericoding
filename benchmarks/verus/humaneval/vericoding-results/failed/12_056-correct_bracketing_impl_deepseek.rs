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
proof fn bracket_counter_helper_lemma(brackets: Seq<char>, pos: nat, count: int, b: bool)
    requires
        pos <= brackets.len(),
        count >= 0,
        exists|i: nat| i <= pos && i as int + count >= 0,
    ensures
        let (final_count, final_valid) = brackets.drop(pos).fold_left((count, b), |(x, valid), c| {
            match c {
                '<' => (x + 1, valid),
                '>' => (x - 1, valid && x - 1 >= 0),
                _ => (x, valid),
            }
        });
        spec_bracketing_helper(brackets).0 == final_count,
        !b ==> !spec_bracketing_helper(brackets).1
{
    if pos < brackets.len() {
        let c = brackets[pos];
        let (new_count, new_valid) = match c {
            '<' => (count + 1, b),
            '>' => (count - 1, b && count - 1 >= 0),
            _ => (count, b),
        };
        bracket_counter_helper_lemma(brackets, pos + 1, new_count, new_valid);
    }
}
/* helper modified by LLM (iteration 5): Fixed spec function call syntax */
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
    /* code modified by LLM (iteration 5): Fixed spec function call syntax */
    let mut count = 0;
    let mut valid = true;
    let chars: Vec<char> = brackets.chars().collect();
    let mut i = 0;
    while i < chars.len()
        invariant
            count >= 0,
            let (partial_count, partial_valid) = chars@.take(i).fold_left(
                (0, true),
                |(x, b), c| match c {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                },
            );
            count == partial_count,
            valid == partial_valid,
            exists|j: nat| j <= i && j as int + count >= 0,
        decreases chars.len() - i
    {
        let c = chars[i];
        match c {
            '<' => {
                count = count + 1;
            }
            '>' => {
                if count <= 0 {
                    valid = false;
                }
                count = count - 1;
            }
            _ => {}
        }
        i = i + 1;
    }
    let result = valid && count == 0;
    proof {
        bracket_counter_helper_lemma(chars@, 0, 0, true);
        assert(spec_bracketing_helper(chars@).1 == valid) by {
            assert(forall|x: (int, bool), y: (int, bool)| x.1 && y.1 ==> x.1 == y.1);
        };
    }
    result
}
// </vc-code>

}
fn main() {}