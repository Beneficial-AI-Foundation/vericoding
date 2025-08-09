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
    let mut is_valid = true;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): Fixed invariant syntax by removing extra braces and properly formatting the invariant condition */
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            count >= i32::MIN,
            count <= i32::MAX,
            {
                let helper_result = spec_bracketing_helper(brackets@.subrange(0, i as int));
                helper_result.0 == count && helper_result.1 == is_valid
            }
    {
        let c = brackets.chars().nth(i).unwrap();
        match c {
            '(' => {
                count += 1;
            }
            ')' => {
                count -= 1;
                if count < 0 {
                    is_valid = false;
                }
            }
            _ => {}
        }
        i += 1;
    }
    
    is_valid && count == 0
}

} // verus!
fn main() {}