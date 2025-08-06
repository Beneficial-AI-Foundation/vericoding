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
    let mut depth: i32 = 0;
    let mut valid = true;
    
    for i in 0..brackets.len()
        invariant
            depth >= 0 ==> valid,
            depth < 0 ==> !valid,
            valid ==> depth >= 0,
            spec_bracketing_helper(brackets@.subrange(0, i as int)) == (depth as int, valid),
    {
        let c = brackets.chars().nth(i).unwrap();
        match c {
            '<' => {
                depth = depth + 1;
            },
            '>' => {
                depth = depth - 1;
                if depth < 0 {
                    valid = false;
                }
            },
            _ => {
                // do nothing for other characters
            }
        }
    }
    
    valid && depth == 0
}

} // verus!
fn main() {}