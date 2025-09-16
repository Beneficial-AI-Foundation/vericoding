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
    /* code modified by LLM (iteration 5): Fixed compilation error by using vstd::string::StrSlice, a public type, to convert the &str to a Vec<char>. */
    let s_slice = vstd::string::StrSlice::from_str(brackets);
    let chars = s_slice.get_chars();

    let mut i: usize = 0;
    let mut count: i32 = 0;
    let mut is_ok: bool = true;

    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            brackets@ == chars@,
            spec_bracketing_helper(brackets@.subrange(0, i as int)) == (count as int, is_ok),
        decreases chars.len() - i
    {
        let c = chars[i];
        
        if c == '(' {
            count = count + 1;
        } else if c == ')' {
            count = count - 1;
            is_ok = is_ok && (count >= 0);
        }
        
        i = i + 1;
    }
    
    return is_ok && count == 0;
}
// </vc-code>

}
fn main() {}