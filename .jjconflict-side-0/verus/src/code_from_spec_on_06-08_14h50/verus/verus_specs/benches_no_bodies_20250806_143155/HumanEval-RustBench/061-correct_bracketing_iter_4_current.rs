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
    let mut valid = true;
    
    let chars = brackets.as_bytes();
    let mut i = 0;
    
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            /* code modified by LLM (iteration 1): Fixed map function signature to accept index and character parameters */
            chars@ == brackets@.map(|idx: int, c: char| c as u8),
            count as int >= -(i as int),
            count as int <= i as int,
            valid ==> count >= 0,
            ({
                let processed = brackets@.subrange(0, i as int);
                let (spec_count, spec_valid) = spec_bracketing_helper(processed);
                valid == spec_valid && count as int == spec_count
            }),
    {
        let c = chars[i] as char;
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
            _ => {
                // do nothing
            }
        }
        i = i + 1;
    }
    
    valid && count == 0
}

} // verus!
fn main() {}