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
spec fn partial_bracketing(brackets: Seq<char>, i: int) -> (ret: (int, bool)) {
    brackets.take(i as nat).fold_left(
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
    let mut i: usize = 0;
    let mut x: i32 = 0;
    let mut b = true;
    while i < brackets.len() {
        invariant
            0 <= i <= brackets.len(),
            (x as int, b) == partial_bracketing(brackets@, i as int),
        match brackets@[i as int] {
            '(' => {
                x = x + 1;
            }
            ')' => {
                x = x - 1;
                b = b && (x + 1 >= 1);
            }
            _ => {}
        }
        i = i + 1;
    }
    b && (x == 0)
}
// </vc-code>

} // verus!
fn main() {}