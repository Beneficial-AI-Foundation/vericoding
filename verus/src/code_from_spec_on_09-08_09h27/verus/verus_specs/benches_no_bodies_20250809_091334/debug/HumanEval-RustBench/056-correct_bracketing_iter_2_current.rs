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
    /* code modified by LLM (iteration 1): Convert str to bytes and work with byte array to avoid unsupported str::len() */
    let bytes = brackets.as_bytes();
    let mut count: i32 = 0;
    let mut i = 0;
    
    while i < bytes.len()
        invariant
            0 <= i <= bytes.len(),
            count >= 0,
            bytes@ == brackets.as_bytes()@,
            spec_bracketing_helper(brackets@.subrange(0, i as int)) == (count as int, true),
    {
        let c = bytes[i] as char;
        if c == '<' {
            count += 1;
        } else if c == '>' {
            if count == 0 {
                return false;
            }
            count -= 1;
        }
        i += 1;
    }
    
    count == 0
}

} // verus!
fn main() {}