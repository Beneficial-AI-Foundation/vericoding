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
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

fn correct_bracketing(brackets: &str) -> (ret: bool)
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
    let mut count: i32 = 0;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            count >= 0,
            spec_bracketing_helper(brackets@.subrange(0, i as int)) == (count as int, true),
    {
        /* code modified by LLM (iteration 1): Fixed compilation error by using brackets.as_bytes()[i] to access characters in executable code */
        let c_byte = brackets.as_bytes()[i];
        let c = c_byte as char;
        
        if c == '(' {
            count = count + 1;
        } else if c == ')' {
            if count == 0 {
                return false;
            }
            count = count - 1;
        }
        
        i = i + 1;
    }
    
    return count == 0;
}

} // verus!
fn main() {}