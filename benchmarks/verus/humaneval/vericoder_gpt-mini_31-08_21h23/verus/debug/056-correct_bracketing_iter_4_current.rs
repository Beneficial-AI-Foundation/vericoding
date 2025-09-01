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
// No additional helpers required for this proof.
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

    let mut i: nat = 0;
    let mut x: int = 0;
    let mut ok: bool = true;
    // Loop over the sequence of chars in the spec view of the string
    while i < n
        invariant i <= n && spec_bracketing_helper(s.slice(0, i)) == (x, ok);
        decreases n - i;
    {
        let c: char = s@[i];
        let new_x: int;
        let new_ok: bool;
        if c == '<' {
            new_x = x + 1;
            new_ok = ok;
        } else if c == '>' {
            new_x = x - 1;
            new_ok = ok && (x - 1 >= 0);
        } else {
            new_x = x;
            new_ok = ok;
        }
        // Show that extending the folded result by this character yields (new_x, new_ok)
        proof {
            assert(s@[i] == c);
            assert(spec_bracketing_helper(s.slice(0, i)) == (x, ok));
            assert(spec_bracketing_helper(s.slice(0, i + 1)) ==
                   match c {
                       '<' => (x + 1, ok),
                       '>' => (x - 1, ok && x - 1 >= 0),
                       _ => (x, ok),
                   });
        }
        x = new_x;
        ok = new_ok;
        i = i + 1;
    }
    let ret: bool = ok && x == 0;
    // Final proof: the invariant at i == len gives that spec_bracketing_helper over full seq
    // equals (x, ok), so spec_bracketing is ok && x == 0.
    proof {
        assert(spec_bracketing_helper(s) == (x, ok));
        assert(spec_bracketing(s) == (ok && x == 0));
    }
    ret
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}