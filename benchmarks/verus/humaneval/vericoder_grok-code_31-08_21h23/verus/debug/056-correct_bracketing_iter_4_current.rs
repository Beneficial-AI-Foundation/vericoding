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
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
// Empty or add any necessary helpers if needed
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    let chars: Vec<char> = brackets.chars().collect();
    let mut i: usize = 0;
    let mut count: i32 = 0;
    let mut valid: bool = true;
    while i < chars.len()
        invariant
            0 <= i as int <= brackets@.len() as int,
            count == (spec_bracketing_helper(brackets@.subrange(0, i as int)).0) as i32,
            valid <==> spec_bracketing_helper(brackets@.subrange(0, i as int)).1,
    {
        let c = chars[i];
        match c {
            '<' => {
                count += 1;
            }
            '>' => {
                if count < 1 {
                    valid = false;
                }
                count -= 1;
            }
            _ => {}
        }
        i += 1;
    }
    let ret = (count == 0) && valid;
    ret
}
// </vc-code>

} // verus!
fn main() {}