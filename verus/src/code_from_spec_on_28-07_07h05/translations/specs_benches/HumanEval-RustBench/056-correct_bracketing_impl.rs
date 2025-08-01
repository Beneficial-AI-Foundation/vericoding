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
    
    /* code modified by LLM (iteration 1): Use brackets@.len() as usize instead of brackets.len() to fix compilation error */
    for i in 0..brackets@.len() as usize
        invariant
            0 <= i <= brackets@.len(),
            count >= 0 ==> valid,
            count < 0 ==> !valid,
            spec_bracketing_helper(brackets@.subrange(0, i as int)) == (count as int, valid),
    {
        let c = brackets.get_char(i);
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
            _ => {}
        }
    }
    
    valid && count == 0
}

} // verus!
fn main() {}