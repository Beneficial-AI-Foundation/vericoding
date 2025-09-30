// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_boolean(seq: Seq<bool>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define int-valued boolean counter */
spec fn add_one_if_true(b: bool) -> int { if b { 1int } else { 0int } }

/* helper modified by LLM (iteration 2): lemma connecting take(i+1) with take(i) */
proof fn lemma_count_boolean_take_step(seq: Seq<bool>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        count_boolean(seq.take(i + 1)) == count_boolean(seq.take(i)) + add_one_if_true(seq[i]),
{
    let t = seq.take(i + 1);
    assert(t.len() == i + 1);
    assert(t.len() > 0);
    assert(t.drop_last() == seq.take(i));
    assert(t.last() == seq[i]);
    assert(count_boolean(t) == count_boolean(t.drop_last()) + add_one_if_true(t.last()));
    assert(count_boolean(seq.take(i + 1)) == count_boolean(t));
    assert(count_boolean(t.drop_last()) == count_boolean(seq.take(i)));
    assert(add_one_if_true(t.last()) == add_one_if_true(seq[i]));
    assert(count_boolean(seq.take(i + 1)) == count_boolean(seq.take(i)) + add_one_if_true(seq[i]));
}
// </vc-helpers>

// <vc-spec>
fn count_true(arr: &Vec<bool>) -> (count: u64)

    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement counting loop with invariant tied to spec count_boolean */
    let mut i: usize = 0;
    let mut c: u64 = 0u64;
    while i < arr.len()
        invariant
            i <= arr.len(),
            0 <= c <= arr.len(),
            c <= i,
            count_boolean(arr@.take(i as int)) == c as int,
        decreases arr.len() - i
    {
        let b = arr[i];
        proof {
            assert(arr@[i as int] == b);
            lemma_count_boolean_take_step(arr@, i as int);
        }
        if b {
            c = c + 1;
        }
        i = i + 1;
    }
    proof {
        assert(arr@.take(arr.len() as int) == arr@);
    }
    c
}
// </vc-code>

}
fn main() {}