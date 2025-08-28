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
// pure-end
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
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
proof fn lemma_max_rcur_bounds(seq: Seq<i32>)
    requires
        seq.len() > 0,
    ensures
        exists|i: int| 0 <= i < seq.len() && max_rcur(seq) == seq[i],
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(max_rcur(seq) == seq[0]);
    } else {
        lemma_max_rcur_bounds(seq.drop_last());
        let last_val = seq.last() as int;
        let sub_max = max_rcur(seq.drop_last());
        if last_val >= sub_max {
            assert(max_rcur(seq) == last_val);
            assert(seq[seq.len() - 1] == last_val);
        } else {
            assert(max_rcur(seq) == sub_max);
            assert(exists|i: int| 0 <= i < seq.len() - 1 && sub_max == seq[i]);
        }
    }
}

proof fn lemma_min_rcur_bounds(seq: Seq<i32>)
    requires
        seq.len() > 0,
    ensures
        exists|i: int| 0 <= i < seq.len() && min_rcur(seq) == seq[i],
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(min_rcur(seq) == seq[0]);
    } else {
        lemma_min_rcur_bounds(seq.drop_last());
        let last_val = seq.last() as int;
        let sub_min = min_rcur(seq.drop_last());
        if last_val <= sub_min {
            assert(min_rcur(seq) == last_val);
            assert(seq[seq.len() - 1] == last_val);
        } else {
            assert(min_rcur(seq) == sub_min);
            assert(exists|i: int| 0 <= i < seq.len() - 1 && sub_min == seq[i]);
        }
    }
}

proof fn lemma_max_rcur_correct(seq: Seq<i32>, max_val: i32)
    requires
        seq.len() > 0,
        forall|j: int| 0 <= j < seq.len() ==> max_val >= seq[j],
        exists|j: int| 0 <= j < seq.len() && max_val == seq[j],
    ensures
        max_val as int == max_rcur(seq),
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(max_rcur(seq) == seq[0]);
        assert(max_val == seq[0]);
    } else {
        let last_val = seq.last() as int;
        let sub_seq = seq.drop_last();
        if last_val == max_val {
            assert(max_rcur(seq) == last_val);
        } else {
            assert(forall|j: int| 0 <= j < sub_seq.len() ==> max_val >= sub_seq[j]);
            assert(exists|j: int| 0 <= j < sub_seq.len() && max_val == sub_seq[j]);
            lemma_max_rcur_correct(sub_seq, max_val);
            assert(max_val as int == max_rcur(sub_seq));
            assert(last_val < max_val);
            assert(max_rcur(seq) == max(last_val, max_rcur(sub_seq)));
            assert(max_rcur(seq) == max_val as int);
        }
    }
}

proof fn lemma_min_rcur_correct(seq: Seq<i32>, min_val: i32)
    requires
        seq.len() > 0,
        forall|j: int| 0 <= j < seq.len() ==> min_val <= seq[j],
        exists|j: int| 0 <= j < seq.len() && min_val == seq[j],
    ensures
        min_val as int == min_rcur(seq),
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(min_rcur(seq) == seq[0]);
        assert(min_val == seq[0]);
    } else {
        let last_val = seq.last() as int;
        let sub_seq = seq.drop_last();
        if last_val == min_val {
            assert(min_rcur(seq) == last_val);
        } else {
            assert(forall|j: int| 0 <= j < sub_seq.len() ==> min_val <= sub_seq[j]);
            assert(exists|j: int| 0 <= j < sub_seq.len() && min_val == sub_seq[j]);
            lemma_min_rcur_correct(sub_seq, min_val);
            assert(min_val as int == min_rcur(sub_seq));
            assert(last_val > min_val);
            assert(min_rcur(seq) == min(last_val, min_rcur(sub_seq)));
            assert(min_rcur(seq) == min_val as int);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max_val: i32 = arr[0];
    let mut min_val: i32 = arr[0];
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> min_val <= arr[j],
            forall|j: int| 0 <= j < i ==> max_val >= arr[j],
            exists|j: int| 0 <= j < i && min_val == arr[j],
            exists|j: int| 0 <= j < i && max_val == arr[j],
        decreases arr.len() - i
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
        lemma_max_rcur_bounds(arr@);
        lemma_min_rcur_bounds(arr@);
        lemma_max_rcur_correct(arr@, max_val);
        lemma_min_rcur_correct(arr@, min_val);
    }

    max_val + min_val
}
// </vc-code>

} // verus!

fn main() {}