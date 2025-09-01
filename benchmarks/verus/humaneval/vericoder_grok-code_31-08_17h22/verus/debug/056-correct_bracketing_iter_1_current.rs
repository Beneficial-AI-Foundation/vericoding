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
    // impl-start
    let mut balance: int = 0;
    let mut all_valid = true;
    let chars = brackets@;

    let mut i = 0;
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            balance == spec_bracketing_helper(chars.subrange(0, i)).0,
            all_valid == spec_bracketing_helper(chars.subrange(0, i)).1,
    {
        let c = chars[i]; // Use @ for indexing
        match c {
            '<' => { balance += 1; }
            '>' => {
                balance -= 1;
                all_valid = all_valid && (balance >= 0);
            }
            _ => {}
        }
        i += 1;
    }
    assert(spec_bracketing_helper(chars) == (balance, all_valid));
    all_valid && balance == 0
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}