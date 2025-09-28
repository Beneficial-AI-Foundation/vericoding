// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): completed proof by revealing function definition and unfolding */
proof fn lemma_min_extends(seq: Seq<i32>, x: i32)
    requires seq.len() > 0
    ensures min_rcur(seq.push(x)) == min(x as int, min_rcur(seq))
{
    reveal(min_rcur);
    let s = seq.push(x);
    assert(min_rcur(s) == min(s.last() as int, min_rcur(s.drop_last())));
    assert(s.last() == x);
    assert(s.drop_last() == seq);
}

/* helper modified by LLM (iteration 5): completed proof by revealing function definition and unfolding */
proof fn lemma_max_extends(seq: Seq<i32>, x: i32)
    requires seq.len() > 0
    ensures max_rcur(seq.push(x)) == max(x as int, max_rcur(seq))
{
    reveal(max_rcur);
    let s = seq.push(x);
    assert(max_rcur(s) == max(s.last() as int, max_rcur(s.drop_last())));
    assert(s.last() == x);
    assert(s.drop_last() == seq);
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant syntax by using a block for invariants */
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut i = 1;
    while i < arr.len()
        invariant {
            1 <= i <= arr.len();
            min_val == min_rcur(arr@[0..i]);
            max_val == max_rcur(arr@[0..i]);
        }
    {
        if arr[i] < min_val {
            min_val = arr[i];
        }
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i += 1;
    }
    min_val + max_val
}
// </vc-code>

}
fn main() {}