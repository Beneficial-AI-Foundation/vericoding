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
// Added no helpers; kept empty as not needed for this fix.
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
    let s: Seq<char> = brackets@;
    let n: nat = s.len();

    let mut v: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i,
            v@ == s.slice(0, i),
    {
        v.push(s@[i]);
        i = i + 1;
    }

    let mut j: nat = 0;
    let mut bal: int = 0;
    let mut ok: bool = true;
    while j < v@.len()
        invariant
            j <= v@.len(),
            (bal, ok) == spec_bracketing_helper(v@.slice(0, j)),
    {
        let c: char = v@[j];
        if c == '(' {
            bal = bal + 1;
        } else if c == ')' {
            bal = bal - 1;
            ok = ok && bal >= 0;
        }
        j = j + 1;
    }

    assert((bal, ok) == spec_bracketing_helper(v@.slice(0, v@.len())));
    assert(v@.slice(0, v@.len()) == v@);
    assert((bal, ok) == spec_bracketing_helper(v@));

    ok && bal == 0
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}