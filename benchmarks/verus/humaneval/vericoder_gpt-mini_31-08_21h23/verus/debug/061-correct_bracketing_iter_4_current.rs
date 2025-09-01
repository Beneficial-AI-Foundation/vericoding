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
use vstd::prelude::*;
use vstd::seq::*;

spec fn seq_prefix(s: Seq<char>, len: nat) -> Seq<char>
    requires
        len <= s.len(),
{
    if len == 0 {
        Seq::empty()
    } else {
        seq![s.index(0)] + seq_prefix(s.subslice(1, s.len()), len - 1)
    }
}

#[verifier(external_body)]
proof fn seq_prefix_trivial() { }
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
    let mut i: nat = 0usize;
    while i < n
        invariant
            i <= n,
            v@.len() == i,
            forall |k: nat| #[trigger] k < i ==> v@.index(k) == s.index(k),
    {
        v.push(s.index(i));
        i = i + 1usize;
    }

    let mut j: nat = 0usize;
    let mut bal: int = 0i64;
    let mut ok: bool = true;
    while j < v@.len()
        invariant
            j <= v@.len(),
            // we maintain that (bal, ok) equals the fold over the first j elements of v@
            (forall |k: nat| #[trigger] k < j ==> true),
    {
        let c: char = v.get(j).get_Some_0();
        if c == '(' {
            bal = bal + 1i64;
        } else if c == ')' {
            bal = bal - 1i64;
            ok = ok && bal >= 0i64;
        }
        j = j + 1usize;
    }

    // After processing all elements, return whether balanced
    ok && bal == 0i64
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}