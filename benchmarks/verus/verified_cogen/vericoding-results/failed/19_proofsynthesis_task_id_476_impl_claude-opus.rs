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
proof fn lemma_max_rcur_update(seq: Seq<i32>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        max_rcur(seq.take(i + 1)) == max(seq[i] as int, max_rcur(seq.take(i))),
    decreases i,
{
    if i == 0 {
        assert(seq.take(1).len() == 1);
        assert(seq.take(1) == seq!(seq[0]));
        assert(max_rcur(seq.take(1)) == seq[0] as int);
    } else {
        let s = seq.take(i + 1);
        assert(s.len() == i + 1);
        assert(s.last() == seq[i]);
        assert(s.drop_last() == seq.take(i));
    }
}

proof fn lemma_min_rcur_update(seq: Seq<i32>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        min_rcur(seq.take(i + 1)) == min(seq[i] as int, min_rcur(seq.take(i))),
    decreases i,
{
    if i == 0 {
        assert(seq.take(1).len() == 1);
        assert(seq.take(1) == seq!(seq[0]));
        assert(min_rcur(seq.take(1)) == seq[0] as int);
    } else {
        let s = seq.take(i + 1);
        assert(s.len() == i + 1);
        assert(s.last() == seq[i]);
        assert(s.drop_last() == seq.take(i));
    }
}

/* helper modified by LLM (iteration 5): Added lemmas for updating max_rcur and min_rcur values */
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
    /* code modified by LLM (iteration 5): Fixed syntax error with i32::MAX constant */
    let mut max_val: i32 = arr[0];
    let mut min_val: i32 = arr[0];
    let mut i: usize = 1;
    
    assert(arr@.take(1) == seq!(arr[0]));
    assert(max_rcur(arr@.take(1)) == arr[0] as int);
    assert(min_rcur(arr@.take(1)) == arr[0] as int);
    
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val as int == max_rcur(arr@.take(i as int)),
            min_val as int == min_rcur(arr@.take(i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
            forall|j: int| 0 <= j < arr.len() ==> i32::MIN / 2 < arr[j] < i32::MAX / 2,
        decreases arr.len() - i,
    {
        proof {
            lemma_max_rcur_update(arr@, i as int);
            lemma_min_rcur_update(arr@, i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        assert(max_val as int == max(arr[i] as int, max_rcur(arr@.take(i as int))));
        
        if arr[i] < min_val {
            min_val = arr[i];
        }
        assert(min_val as int == min(arr[i] as int, min_rcur(arr@.take(i as int))));
        
        i += 1;
    }
    
    assert(arr@.take(arr.len() as int) == arr@);
    assert(max_val as int + min_val as int < (i32::MAX as int));
    assert(max_val as int + min_val as int > (i32::MIN as int));
    max_val + min_val
}
// </vc-code>

}
fn main() {}