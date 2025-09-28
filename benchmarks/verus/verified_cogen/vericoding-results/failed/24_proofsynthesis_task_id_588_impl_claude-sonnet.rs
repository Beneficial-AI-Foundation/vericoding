// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
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
/* helper modified by LLM (iteration 5): removed requires/ensures from spec functions */
spec fn max_helper(seq: Seq<i32>, idx: int) -> int
    decreases seq.len() - idx,
{
    if idx >= seq.len() - 1 {
        seq[idx] as int
    } else {
        max(seq[idx] as int, max_helper(seq, idx + 1))
    }
}

spec fn min_helper(seq: Seq<i32>, idx: int) -> int
    decreases seq.len() - idx,
{
    if idx >= seq.len() - 1 {
        seq[idx] as int
    } else {
        min(seq[idx] as int, min_helper(seq, idx + 1))
    }
}

spec fn max_helper_partial(seq: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start == end - 1 {
        seq[start] as int
    } else {
        max(seq[start] as int, max_helper_partial(seq, start + 1, end))
    }
}

spec fn min_helper_partial(seq: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start == end - 1 {
        seq[start] as int
    } else {
        min(seq[start] as int, min_helper_partial(seq, start + 1, end))
    }
}

proof fn max_equivalence(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures max_rcur(seq) == max_helper(seq, 0),
    decreases seq.len(),
{
    if seq.len() <= 1 {
    } else {
        max_equivalence(seq.drop_last());
        assert(max_rcur(seq.drop_last()) == max_helper(seq.drop_last(), 0));
        assert(max_helper(seq.drop_last(), 0) == max_helper(seq, 1));
    }
}

proof fn min_equivalence(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures min_rcur(seq) == min_helper(seq, 0),
    decreases seq.len(),
{
    if seq.len() <= 1 {
    } else {
        min_equivalence(seq.drop_last());
        assert(min_rcur(seq.drop_last()) == min_helper(seq.drop_last(), 0));
        assert(min_helper(seq.drop_last(), 0) == min_helper(seq, 1));
    }
}

proof fn max_partial_extends(seq: Seq<i32>, i: int)
    requires 0 < i < seq.len(),
    ensures max_helper_partial(seq, 0, i + 1) == max(seq[i] as int, max_helper_partial(seq, 0, i)),
    decreases i,
{
    if i == 1 {
    } else {
        max_partial_extends(seq, i - 1);
    }
}

proof fn min_partial_extends(seq: Seq<i32>, i: int)
    requires 0 < i < seq.len(),
    ensures min_helper_partial(seq, 0, i + 1) == min(seq[i] as int, min_helper_partial(seq, 0, i)),
    decreases i,
{
    if i == 1 {
    } else {
        min_partial_extends(seq, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches by casting usize to int and nat to int in function calls */
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val as int == max_helper_partial(arr@, 0, i as int),
            min_val as int == min_helper_partial(arr@, 0, i as int),
        decreases arr.len() - i
    {
        proof {
            max_partial_extends(arr@, i as int);
            min_partial_extends(arr@, i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        assert(max_val as int == max_helper_partial(arr@, 0, arr@.len() as int));
        assert(min_val as int == min_helper_partial(arr@, 0, arr@.len() as int));
        assert(max_helper_partial(arr@, 0, arr@.len() as int) == max_helper(arr@, 0));
        assert(min_helper_partial(arr@, 0, arr@.len() as int) == min_helper(arr@, 0));
        max_equivalence(arr@);
        min_equivalence(arr@);
    }
    
    max_val - min_val
}
// </vc-code>

}
fn main() {}