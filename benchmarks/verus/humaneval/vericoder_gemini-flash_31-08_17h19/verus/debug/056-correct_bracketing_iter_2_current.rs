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
fn fold_left_lemma<A, F>(s: Seq<A>, init: A, f: F, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.fold_left(init, f).take(i).last() == (s.take(i)).fold_left(init, f),
{
    if i > 0 {
        fold_left_lemma(s, init, f, i - 1);
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
    let mut x: int = 0;
    let mut b: bool = true;
    let brackets_seq = brackets@;

    let len_as_int = brackets_seq.len();

    let mut k: nat = 0;
    while (k as int) < len_as_int
        invariant
            0 <= k as int <= len_as_int,
            (x, b) == spec_bracketing_helper(brackets_seq.take(k as int)),
    {
        let c = brackets_seq[k as int];
        match c {
            '<' => {
                x = x + 1;
            }
            '>' => {
                x = x - 1;
                b = b && x >= 0;
            }
            _ => {
            }
        }
        k = (k + 1) as nat;
    }

    b && x == 0
}
// </vc-code>

} // verus!
fn main() {}