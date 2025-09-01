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
// No helpers needed for this verification.
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
    let seq: Seq<char> = brackets@;
    let v: Vec<char> = brackets.chars().collect();
    proof { assert(v@ == seq); }
    let n: usize = v.len();
    let mut i: usize = 0usize;
    let mut acc: i64 = 0;
    let mut ok: bool = true;
    while i < n
        invariant i <= n;
        invariant acc as int == spec_bracketing_helper(seq[..i]).0;
        invariant ok == spec_bracketing_helper(seq[..i]).1;
    {
        let c = v[i];
        if c == '(' {
            acc += 1;
        } else if c == ')' {
            acc -= 1;
            if acc < 0 {
                ok = false;
            }
        }
        i += 1;
    }
    let ret: bool = ok && acc == 0;
    proof {
        assert(acc as int == spec_bracketing_helper(seq).0);
        assert(ok == spec_bracketing_helper(seq).1);
        assert(ret == spec_bracketing(seq));
    }
    ret
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}