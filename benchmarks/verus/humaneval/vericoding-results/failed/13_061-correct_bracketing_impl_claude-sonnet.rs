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
/* helper modified by LLM (iteration 5): added helper function to convert string to Seq<char> and process it */
fn correct_bracketing_helper(brackets: Vec<char>) -> (ret: bool)
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    ensures
        ret <==> spec_bracketing(brackets@),
{
    let mut count: i32 = 0;
    let mut valid: bool = true;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            i <= brackets@.len(),
            count >= -brackets@.len(),
            count <= brackets@.len(),
            valid ==> count >= 0,
        decreases
            brackets@.len() - i,
    {
        let c = brackets[i];
        match c {
            '(' => {
                count = count + 1;
            },
            ')' => {
                count = count - 1;
                if count < 0 {
                    valid = false;
                }
            },
            _ => {}
        }
        i = i + 1;
    }
    
    valid && count == 0
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
/* code modified by LLM (iteration 5): convert string to Vec<char> to avoid unsupported str::len() */
{
    let chars: Vec<char> = brackets.chars().collect();
    correct_bracketing_helper(chars)
}
// </vc-code>

}
fn main() {}