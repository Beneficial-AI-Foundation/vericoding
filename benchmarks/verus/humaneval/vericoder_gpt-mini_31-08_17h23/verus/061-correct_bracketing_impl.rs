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
proof fn bracketing_fold_rec(seq: Seq<char>, n: nat) -> (ret: (int, bool))
    ensures ret == spec_bracketing_helper(seq[..n])
    decreases n
{
    if n == 0 {
        return (0, true);
    } else {
        let (acc_prev, ok_prev) = bracketing_fold_rec(seq, n - 1);
        let c: char = seq@[n - 1];
        if c == '(' {
            return (acc_prev + 1, ok_prev);
        } else if c == ')' {
            return (acc_prev - 1, ok_prev && acc_prev - 1 >= 0);
        } else {
            return (acc_prev, ok_prev);
        }
    }
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
    let seq: Seq<char> = brackets@;
    let n: nat = seq.len();
    let p = bracketing_fold_rec(seq, n);
    let ret: bool = p.1 && p.0 == 0;
    proof {
        assert(p == spec_bracketing_helper(seq));
        assert(ret == spec_bracketing(seq));
    }
    ret
}
// </vc-code>

} // verus!
fn main() {}