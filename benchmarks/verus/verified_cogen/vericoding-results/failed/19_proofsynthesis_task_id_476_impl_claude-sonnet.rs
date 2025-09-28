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
/* helper modified by LLM (iteration 5): fixed type mismatches with nat/int conversions */
proof fn max_rcur_bounds(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures forall|i: int| 0 <= i < seq.len() ==> #[trigger] seq[i] as int <= max_rcur(seq),
    decreases seq.len(),
{
    if seq.len() == 1 {
        // Base case: single element
    } else {
        // Inductive case
        max_rcur_bounds(seq.drop_last());
        // max_rcur(seq) = max(seq.last() as int, max_rcur(seq.drop_last()))
        // For i < seq.len() - 1: seq[i] <= max_rcur(seq.drop_last()) <= max_rcur(seq)
        // For i = seq.len() - 1: seq[i] = seq.last() <= max_rcur(seq)
    }
}

proof fn min_rcur_bounds(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures forall|i: int| 0 <= i < seq.len() ==> min_rcur(seq) <= #[trigger] seq[i] as int,
    decreases seq.len(),
{
    if seq.len() == 1 {
        // Base case: single element
    } else {
        // Inductive case
        min_rcur_bounds(seq.drop_last());
        // min_rcur(seq) = min(seq.last() as int, min_rcur(seq.drop_last()))
        // For i < seq.len() - 1: min_rcur(seq) <= min_rcur(seq.drop_last()) <= seq[i]
        // For i = seq.len() - 1: min_rcur(seq) <= seq.last() = seq[i]
    }
}

proof fn max_min_rcur_in_range(seq: Seq<i32>)
    requires
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < #[trigger] seq[i] < i32::MAX / 2,
    ensures
        i32::MIN < max_rcur(seq) + min_rcur(seq) < i32::MAX,
{
    max_rcur_bounds(seq);
    min_rcur_bounds(seq);
    // From bounds: min_rcur(seq) <= seq[0] as int and seq[0] as int <= max_rcur(seq)
    // From precondition: i32::MIN / 2 < seq[0] < i32::MAX / 2
    // Therefore: i32::MIN / 2 < min_rcur(seq) <= seq[0] <= max_rcur(seq) < i32::MAX / 2
    // So: i32::MIN < min_rcur(seq) + max_rcur(seq) < i32::MAX
}

proof fn max_rcur_subrange_equiv(seq: Seq<i32>, end: int)
    requires
        seq.len() > 0,
        1 <= end <= seq.len(),
    ensures
        max_rcur(seq.subrange(0, end)) == max_rcur(seq.take(end as nat)),
    decreases end,
{
    if end == 1 {
        assert(seq.subrange(0, 1) =~= seq.take(1));
    } else {
        max_rcur_subrange_equiv(seq, end - 1);
        assert(seq.subrange(0, end) =~= seq.take(end as nat));
    }
}

proof fn min_rcur_subrange_equiv(seq: Seq<i32>, end: int)
    requires
        seq.len() > 0,
        1 <= end <= seq.len(),
    ensures
        min_rcur(seq.subrange(0, end)) == min_rcur(seq.take(end as nat)),
    decreases end,
{
    if end == 1 {
        assert(seq.subrange(0, 1) =~= seq.take(1));
    } else {
        min_rcur_subrange_equiv(seq, end - 1);
        assert(seq.subrange(0, end) =~= seq.take(end as nat));
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
    /* code modified by LLM (iteration 5): fixed type cast for take() method argument */
    proof {
        max_min_rcur_in_range(arr@);
    }
    
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val as int == max_rcur(arr@.take(i as nat)),
            min_val as int == min_rcur(arr@.take(i as nat)),
        decreases arr.len() - i
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.take(arr.len()) =~= arr@);
        assert(max_val as int == max_rcur(arr@));
        assert(min_val as int == min_rcur(arr@));
        max_min_rcur_in_range(arr@);
    }
    
    max_val + min_val
}
// </vc-code>

}
fn main() {}