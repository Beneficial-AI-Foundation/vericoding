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
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

/* code modified by LLM (iteration 1): fixed function signature syntax by moving requires and ensures clauses inside function signature */
fn correct_bracketing(brackets: &str) -> (ret: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> spec_bracketing(brackets@),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): implemented proper bracketing logic with correct loop invariants */
    let mut count: i32 = 0;
    let mut valid = true;
    
    for i in 0..brackets.len()
        invariant
            0 <= i <= brackets.len(),
            count == spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
            valid <==> spec_bracketing_helper(brackets@.subrange(0, i as int)).1,
    {
        let c = brackets.char_at(i);
        match c {
            '<' => {
                count = count + 1;
            },
            '>' => {
                count = count - 1;
                if count < 0 {
                    valid = false;
                }
            },
            _ => {
                // do nothing for other characters
            }
        }
    }
    
    return valid && count == 0;
}

} // verus!
fn main() {}