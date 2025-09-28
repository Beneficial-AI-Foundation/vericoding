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
/* helper modified by LLM (iteration 5): combined multiple requires clauses into one to fix compilation error */
spec fn min_up_to(seq: Seq<i32>, i: int) -> int
    decreases seq.len() - i
{
    if i == 0 {
        i32::MIN as int
    } else {
        min(seq@[(i-1) as int] as int, min_up_to(seq, i-1))
    }
}

spec fn max_up_to(seq: Seq<i32>, i: int) -> int
    decreases seq.len() - i
{
    if i == 0 {
        i32::MAX as int
    } else {
        max(seq@[(i-1) as int] as int, max_up_to(seq, i-1))
    }
}
/* helper modified by LLM (iteration 5): combined multiple requires clauses into one to fix compilation error */
proof fn lemma_min_up_to_equals_min_rcur(seq: Seq<i32>, i: int)
    requires seq.len() > 0 && 1 <= i <= seq.len()
    ensures min_up_to(seq, i) == min_rcur(seq.take(i))
{
    if i == 1 {
        assert seq.take(1).first() as int == seq@[0] as int;
        assert min_up_to(seq, 1) == seq@[0] as int;
    } else {
        lemma_min_up_to_equals_min_rcur(seq, i-1);
        assert min_rcur(seq.take(i)) == min(seq.take(i).last() as int, min_rcur(seq.take(i).drop_last()));
        assert seq.take(i).last() as int == seq@[(i-1) as int] as int;
        assert min_rcur(seq.take(i-1)) == min_rcur(seq.take(i).drop_last());
    }
}
/* helper modified by LLM (iteration 5): combined multiple requires clauses into one to fix compilation error */
proof fn lemma_max_up_to_equals_max_rcur(seq: Seq<i32>, i: int)
    requires seq.len() > 0 && 1 <= i <= seq.len()
    ensures max_up_to(seq, i) == max_rcur(seq.take(i))
{
    if i == 1 {
        assert seq.take(1).first() as int == seq@[0] as int;
        assert max_up_to(seq, 1) == seq@[0] as int;
    } else {
        lemma_max_up_to_equals_max_rcur(seq, i-1);
        assert max_rcur(seq.take(i)) == max(seq.take(i).last() as int, max_rcur(seq.take(i).drop_last()));
        assert seq.take(i).last() as int == seq@[(i-1) as int] as int;
        assert max_rcur(seq.take(i-1)) == max_rcur(seq.take(i).drop_last());
    }
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
{
    /* code modified by LLM (iteration 5): implemented loop to compute min and max with invariants */
    let mut min_val: i32 = arr[0];
    let mut max_val: i32 = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            min_val == min_up_to(arr@, i),
            max_val == max_up_to(arr@, i),
    {
        let current = arr[i];
        if current < min_val {
            min_val = current;
        }
        if current > max_val {
            max_val = current;
        }
        i = i + 1;
    }
    proof { lemma_min_up_to_equals_min_rcur(arr@, arr.len()); }
    proof { lemma_max_up_to_equals_max_rcur(arr@, arr.len()); }
    min_val + max_val
}
// </vc-code>

}
fn main() {}