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
/* helper modified by LLM (iteration 4): fixed int type usage in exec code */
fn process_bracket_char(count: i32, c: char) -> (result: i32)
    requires
        count >= 0,
    ensures
        if c == '<' { result == count + 1 }
        else if c == '>' && count > 0 { result == count - 1 }
        else if c == '>' && count == 0 { result == -1 }
        else { result == count },
{
    if c == '<' {
        count + 1
    } else if c == '>' {
        if count == 0 {
            -1
        } else {
            count - 1
        }
    } else {
        count
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
/* code modified by LLM (iteration 4): use i32 instead of int for exec code */
{
    let mut count: i32 = 0;
    for c in brackets.chars() {
        count = process_bracket_char(count, c);
        if count < 0 {
            return false;
        }
    }
    count == 0
}
// </vc-code>

}
fn main() {}