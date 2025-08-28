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
spec fn max_iter_spec(seq: Seq<i32>, i: int) -> int
    recommends 0 <= i < seq.len()
    decreases i
{
    if i == 0 {
        seq[0] as int
    } else {
        max(seq[i] as int, max_iter_spec(seq, i - 1))
    }
}

spec fn min_iter_spec(seq: Seq<i32>, i: int) -> int
    recommends 0 <= i < seq.len()
    decreases i
{
    if i == 0 {
        seq[0] as int
    } else {
        min(seq[i] as int, min_iter_spec(seq, i - 1))
    }
}

proof fn lemma_max_rcur_eq_iter(seq: Seq<i32>)
    requires seq.len() > 0
    ensures max_rcur(seq) == max_iter_spec(seq, seq.len() - 1)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(seq.first() == seq[0]);
    } else {
        lemma_max_rcur_eq_iter(seq.drop_last());
        assert(seq.drop_last().len() == seq.len() - 1);
        assert(seq.last() == seq[seq.len() - 1]);
        assert(max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())));
        assert(max_rcur(seq.drop_last()) == max_iter_spec(seq.drop_last(), seq.drop_last().len() - 1));
        assert(seq.drop_last().len() - 1 == seq.len() - 2);
        assert(forall|j: int| 0 <= j < seq.drop_last().len() ==> seq.drop_last()[j] == seq[j]);
        assert(max_iter_spec(seq.drop_last(), seq.len() - 2) == max_iter_spec(seq, seq.len() - 2));
        assert(max_iter_spec(seq, seq.len() - 1) == max(seq[seq.len() - 1] as int, max_iter_spec(seq, seq.len() - 2)));
    }
}

proof fn lemma_min_rcur_eq_iter(seq: Seq<i32>)
    requires seq.len() > 0
    ensures min_rcur(seq) == min_iter_spec(seq, seq.len() - 1)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(seq.first() == seq[0]);
    } else {
        lemma_min_rcur_eq_iter(seq.drop_last());
        assert(seq.drop_last().len() == seq.len() - 1);
        assert(seq.last() == seq[seq.len() - 1]);
        assert(min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())));
        assert(min_rcur(seq.drop_last()) == min_iter_spec(seq.drop_last(), seq.drop_last().len() - 1));
        assert(seq.drop_last().len() - 1 == seq.len() - 2);
        assert(forall|j: int| 0 <= j < seq.drop_last().len() ==> seq.drop_last()[j] == seq[j]);
        assert(min_iter_spec(seq.drop_last(), seq.len() - 2) == min_iter_spec(seq, seq.len() - 2));
        assert(min_iter_spec(seq, seq.len() - 1) == min(seq[seq.len() - 1] as int, min_iter_spec(seq, seq.len() - 2)));
    }
}

proof fn lemma_max_bounds(seq: Seq<i32>, i: int)
    requires 0 <= i < seq.len(),
        forall|j: int| 0 <= j < seq.len() ==> i32::MIN / 2 < seq[j] < i32::MAX / 2
    ensures i32::MIN / 2 < max_iter_spec(seq, i) < i32::MAX / 2
    decreases i
{
    if i == 0 {
    } else {
        lemma_max_bounds(seq, i - 1);
    }
}

proof fn lemma_min_bounds(seq: Seq<i32>, i: int)
    requires 0 <= i < seq.len(),
        forall|j: int| 0 <= j < seq.len() ==> i32::MIN / 2 < seq[j] < i32::MAX / 2
    ensures i32::MIN / 2 < min_iter_spec(seq, i) < i32::MAX / 2
    decreases i
{
    if i == 0 {
    } else {
        lemma_min_bounds(seq, i - 1);
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
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val as int == max_iter_spec(arr@, (i - 1) as int),
            min_val as int == min_iter_spec(arr@, (i - 1) as int),
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
        lemma_max_rcur_eq_iter(arr@);
        lemma_min_rcur_eq_iter(arr@);
        lemma_max_bounds(arr@, (arr.len() - 1) as int);
        lemma_min_bounds(arr@, (arr.len() - 1) as int);
        assert(max_val as int == max_rcur(arr@));
        assert(min_val as int == min_rcur(arr@));
    }
    
    max_val - min_val
}
// </vc-code>

} // verus!

fn main() {}