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
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>

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
    let n = brackets.len();
    let mut count = 0;
    let mut valid = true;
    let mut i = 0;
    while i < n {
        invariant i <= n && valid == spec_bracketing_helper(brackets@.slice(0, i)).1 && (valid ==> (count == spec_bracketing_helper(brackets@.slice(0, i)).0))
        let c = brackets.chars().nth(i).unwrap();
        match c {
            '(' => {
                count += 1;
            }
            ')' => {
                if count > 0 {
                    count -= 1;
                } else {
                    valid = false;
                }
            }
            _ => {}
        }
        i += 1;
    }
    return valid && count == 0;
}
// </vc-code>

} // verus!
fn main() {}