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
/* helper modified by LLM (iteration 5): cast seq.len to int for take */ spec fn slice_id(seq: Seq<i32>) -> bool { seq.take(seq.len() as int) == seq }
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
    /* code modified by LLM (iteration 5): use usize loop index and spec casts */
    let mut i: usize = 1;
    let mut cur_max: i32 = arr[0];
    let mut cur_min: i32 = arr[0];
    while i < arr.len()
        invariant
            1 <= i as int,
            i as int <= arr.len() as int,
            cur_max as int == max_rcur(arr@.take(i as int)),
            cur_min as int == min_rcur(arr@.take(i as int)),
        decreases
            arr.len() as int - i as int
    {
        let v: i32 = arr[i];
        let old_max: i32 = cur_max;
        let old_min: i32 = cur_min;
        if v > old_max {
            cur_max = v;
        }
        if v < old_min {
            cur_min = v;
        }
        proof {
            assert(old_max as int == max_rcur(arr@.take(i as int)));
            assert(old_min as int == min_rcur(arr@.take(i as int)));
            assert(max_rcur(arr@.take((i as int) + 1)) == max(arr@[(i as int)] as int, max_rcur(arr@.take(i as int))));
            assert(min_rcur(arr@.take((i as int) + 1)) == min(arr@[(i as int)] as int, min_rcur(arr@.take(i as int))));
            if v > old_max {
                assert(cur_max as int == arr@[(i as int)] as int);
                assert(cur_max as int == max(arr@[(i as int)] as int, old_max as int));
            } else {
                assert(arr@[(i as int)] <= old_max);
                assert(cur_max as int == old_max as int);
                assert(cur_max as int == max(arr@[(i as int)] as int, old_max as int));
            }
            if v < old_min {
                assert(cur_min as int == arr@[(i as int)] as int);
                assert(cur_min as int == min(arr@[(i as int)] as int, old_min as int));
            } else {
                assert(arr@[(i as int)] >= old_min);
                assert(cur_min as int == old_min as int);
                assert(cur_min as int == min(arr@[(i as int)] as int, old_min as int));
            }
            assert(cur_max as int == max_rcur(arr@.take((i as int) + 1)));
            assert(cur_min as int == min_rcur(arr@.take((i as int) + 1)));
        }
        i += 1;
    }
    proof {
        assert(cur_max as int == max_rcur(arr@.take(arr.len() as int)));
        assert(cur_min as int == min_rcur(arr@.take(arr.len() as int)));
        assert(slice_id(arr@));
        assert(max_rcur(arr@.take(arr.len() as int)) == max_rcur(arr@));
        assert(min_rcur(arr@.take(arr.len() as int)) == min_rcur(arr@));
        assert(cur_max as int == max_rcur(arr@));
        assert(cur_min as int == min_rcur(arr@));
    }
    cur_max - cur_min
}
// </vc-code>

}
fn main() {}