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
/* helper modified by LLM (iteration 5): convert string to char sequence and check bracketing */
fn check_bracketing_chars(brackets: &str) -> (ret: bool)
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    ensures
        ret <==> spec_bracketing(brackets@),
{
    let mut depth: i32 = 0;
    let mut i: usize = 0;
    let chars: Vec<char> = brackets.chars().collect();
    
    while i < chars.len()
        invariant
            i <= chars.len(),
            chars@ == brackets@,
            depth >= 0,
            depth == spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
    {
        let c = chars[i];
        
        if c == '<' {
            depth += 1;
        } else if c == '>' {
            depth -= 1;
            if depth < 0 {
                return false;
            }
        }
        
        i += 1;
    }
    
    depth == 0
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
    /* code modified by LLM (iteration 5): use helper function that works with chars to match spec */
    check_bracketing_chars(brackets)
}
// </vc-code>

}
fn main() {}