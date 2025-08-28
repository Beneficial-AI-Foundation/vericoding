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
// pure-end
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// pure-end

// <vc-helpers>
proof fn max_rcur_is_max(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures forall|i: int| 0 <= i < seq.len() ==> max_rcur(seq) >= seq[i] as int,
    decreases seq.len(),
{
    if seq.len() <= 1 {
        assert(seq.first() as int >= seq.first() as int);
    } else {
        max_rcur_is_max(seq.drop_last());
        assert(max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())));
        assert(max_rcur(seq) >= seq.last() as int);
        assert(max_rcur(seq) >= max_rcur(seq.drop_last()));
        assert(forall|i: int| 0 <= i < seq.len() - 1 ==> max_rcur(seq.drop_last()) >= seq[i] as int);
        assert(forall|i: int| 0 <= i < seq.len() ==> max_rcur(seq) >= seq[i] as int);
    }
}

proof fn min_rcur_is_min(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures forall|i: int| 0 <= i < seq.len() ==> min_rcur(seq) <= seq[i] as int,
    decreases seq.len(),
{
    if seq.len() <= 1 {
        assert(seq.first() as int <= seq.first() as int);
    } else {
        min_rcur_is_min(seq.drop_last());
        assert(min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())));
        assert(min_rcur(seq) <= seq.last() as int);
        assert(min_rcur(seq) <= min_rcur(seq.drop_last()));
        assert(forall|i: int| 0 <= i < seq.len() - 1 ==> min_rcur(seq.drop_last()) <= seq[i] as int);
        assert(forall|i: int| 0 <= i < seq.len() ==> min_rcur(seq) <= seq[i] as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max_val: i32 = arr[0];
    let mut min_val: i32 = arr[0];
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: usize| 0 <= k < i ==> max_val >= arr[k],
            forall|k: usize| 0 <= k < i ==> min_val <= arr[k],
            forall|k: usize| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2,
        decreases arr.len() - i,
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i = i + 1;
    }

    proof {
        max_rcur_is_max(arr@);
        min_rcur_is_min(arr@);
        assert(forall|i: usize| 0 <= i < arr.len() ==> max_val >= arr[i]);
        assert(forall|i: usize| 0 <= i < arr.len() ==> min_val <= arr[i]);
        assert(max_val as int == max_rcur(arr@));
        assert(min_val as int == min_rcur(arr@));
    }

    (max_val - min_val)
}
// </vc-code>

} // verus!

fn main() {}