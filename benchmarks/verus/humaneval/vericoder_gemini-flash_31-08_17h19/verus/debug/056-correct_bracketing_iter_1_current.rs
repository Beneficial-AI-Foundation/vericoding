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
        forall|j: int| 0 <= j < i ==> #[trigger] f(s.fold_left(init, f).take(j).last(), s[j]) == s.fold_left(init, f).take(j + 1).last()
        // forall|x: int, y: int| #[trigger] f(x, y) is well-defined
    ensures
        s.fold_left(init, f).take(i).last() == (s.take(i)).fold_left(init, f)
    decreases i
{
    if i > 0 {
        fold_left_lemma(s, init, f, i - 1);
        assert(s.fold_left(init, f).take(i).last() == f(s.fold_left(init, f).take(i - 1).last(), s[i - 1]));
        assert(s.take(i).fold_left(init, f) == f(s.take(i - 1).fold_left(init, f), s[i - 1]));
        assert(s.fold_left(init, f).take(i - 1).last() == (s.take(i - 1)).fold_left(init, f));
    } else {
        assert(s.fold_left(init, f).take(0).last() == init);
        assert(s.take(0).fold_left(init, f) == init);
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

    // Theorem: forall k in 0..len:
    // (x, b) has the same value as spec_bracketing_helper(brackets_seq.take(k))
    // x and b must be related to spec_bracketing_helper(brackets_seq.take(k))
    // (x, b) == spec_bracketing_helper(brackets_seq.take(k))
    // in the loop we mutate x and b according to the spec
    // (x,b) is invariant in each step

    // To preserve the invariant for x and b
    // we need to update values in the loop:
    // x changes to  x + 1 or x - 1 and b changes to b && x - 1 >= 0
    // so x becomes next_x and b becomes next_b
    // we can use the loop iteration variable to denote the next index in the sequence

    // Invariant:
    // For `k < brackets_seq.len()`, if we let `p_k = spec_bracketing_helper(brackets_seq.take(k))`
    // then `x` (current value) is `p_k.0` and `b` (current value) is `p_k.1`

    // The invariant must be `(x, b) == spec_bracketing_helper(brackets_seq.take(k as int))`
    // where `k` is the loop variable.
    // k is the number of elements processed thus far.
    // When k becomes 0, its (x,b) is (0, true)
    // When k becomes brackets_seq.len(), (x,b) is spec_bracketing_helper(brackets_seq)

    // The value of spec_bracketing_helper(brackets_seq.take(k)).0 always needs to be available
    // and if we let p = spec_bracketing_helper(brackets_seq.take(k)) then x == p.0 and b == p.1

    let mut k: int = 0;
    while k < len_as_int
        invariant
            0 <= k <= len_as_int,
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
        k = k + 1;
    }

    // After the loop, k == len_as_int. So the invariant becomes:
    // (x, b) == spec_bracketing_helper(brackets_seq.take(len_as_int))
    // (x, b) == spec_bracketing_helper(brackets_seq)
    // The final result `ret` is `b && x == 0`
    // This is `spec_bracketing_helper(brackets_seq).1 && spec_bracketing_helper(brackets_seq).0 == 0`
    // which is exactly `spec_bracketing(brackets_seq)`

    b && x == 0
}
// </vc-code>

} // verus!
fn main() {}