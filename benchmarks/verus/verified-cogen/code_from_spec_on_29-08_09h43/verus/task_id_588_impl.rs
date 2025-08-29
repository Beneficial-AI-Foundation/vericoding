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
    decreases seq.len() - i,
{
    if i >= seq.len() - 1 {
        seq[i] as int
    } else {
        max(seq[i] as int, max_iter_spec(seq, i + 1))
    }
}

spec fn min_iter_spec(seq: Seq<i32>, i: int) -> int
    decreases seq.len() - i,
{
    if i >= seq.len() - 1 {
        seq[i] as int
    } else {
        min(seq[i] as int, min_iter_spec(seq, i + 1))
    }
}

spec fn max_up_to(seq: Seq<i32>, i: int) -> int
    decreases i
{
    /* code modified by LLM (iteration 5): fixed bounds check for sequence access */
    if i == 0 {
        seq[0] as int
    } else {
        max(seq[i] as int, max_up_to(seq, i - 1))
    }
}

spec fn min_up_to(seq: Seq<i32>, i: int) -> int
    decreases i
{
    /* code modified by LLM (iteration 5): fixed bounds check for sequence access */
    if i == 0 {
        seq[0] as int
    } else {
        min(seq[i] as int, min_up_to(seq, i - 1))
    }
}

proof fn lemma_max_rcur_equals_max_iter(seq: Seq<i32>)
    requires seq.len() > 0
    ensures max_rcur(seq) == max_iter_spec(seq, 0)
    decreases seq.len()
{
    /* code modified by LLM (iteration 5): correct induction proof structure */
    if seq.len() <= 1 {
    } else {
        lemma_max_rcur_equals_max_iter(seq.drop_last());
        assert(max_rcur(seq.drop_last()) == max_iter_spec(seq.drop_last(), 0));
        assert(seq.drop_last().len() == seq.len() - 1);
        lemma_max_iter_drop_last_relation(seq);
    }
}

proof fn lemma_min_rcur_equals_min_iter(seq: Seq<i32>)
    requires seq.len() > 0
    ensures min_rcur(seq) == min_iter_spec(seq, 0)
    decreases seq.len()
{
    /* code modified by LLM (iteration 5): correct induction proof structure */
    if seq.len() <= 1 {
    } else {
        lemma_min_rcur_equals_min_iter(seq.drop_last());
        assert(min_rcur(seq.drop_last()) == min_iter_spec(seq.drop_last(), 0));
        assert(seq.drop_last().len() == seq.len() - 1);
        lemma_min_iter_drop_last_relation(seq);
    }
}

proof fn lemma_max_iter_drop_last_relation(seq: Seq<i32>)
    requires seq.len() > 1
    ensures max_iter_spec(seq.drop_last(), 0) == max_iter_spec(seq, 1)
    decreases seq.len() - 1
{
    /* code modified by LLM (iteration 5): prove relation between original and truncated sequences */
    if seq.len() == 2 {
        assert(max_iter_spec(seq.drop_last(), 0) == seq[0] as int);
        assert(max_iter_spec(seq, 1) == seq[1] as int);
    } else {
        lemma_max_iter_drop_last_relation(seq.subrange(1, seq.len() as int));
    }
}

proof fn lemma_min_iter_drop_last_relation(seq: Seq<i32>)
    requires seq.len() > 1
    ensures min_iter_spec(seq.drop_last(), 0) == min_iter_spec(seq, 1)
    decreases seq.len() - 1
{
    /* code modified by LLM (iteration 5): prove relation between original and truncated sequences */
    if seq.len() == 2 {
        assert(min_iter_spec(seq.drop_last(), 0) == seq[0] as int);
        assert(min_iter_spec(seq, 1) == seq[1] as int);
    } else {
        lemma_min_iter_drop_last_relation(seq.subrange(1, seq.len() as int));
    }
}

proof fn lemma_max_up_to_extends(seq: Seq<i32>, i: int)
    requires 0 <= i < seq.len()
    ensures max_up_to(seq, i) == max_iter_spec(seq, 0)
    decreases i
{
    /* code modified by LLM (iteration 5): correct proof connecting max_up_to with max_iter_spec */
    if i == 0 {
        assert(max_up_to(seq, 0) == seq[0] as int);
        if seq.len() == 1 {
            assert(max_iter_spec(seq, 0) == seq[0] as int);
        } else {
            lemma_max_up_to_extends(seq, seq.len() - 1);
        }
    } else {
        lemma_max_up_to_extends(seq, i - 1);
        assert(max_up_to(seq, i - 1) == max_iter_spec(seq, 0));
        lemma_max_up_to_monotone(seq, i - 1, i);
    }
}

proof fn lemma_min_up_to_extends(seq: Seq<i32>, i: int)
    requires 0 <= i < seq.len()
    ensures min_up_to(seq, i) == min_iter_spec(seq, 0)
    decreases i
{
    /* code modified by LLM (iteration 5): correct proof connecting min_up_to with min_iter_spec */
    if i == 0 {
        assert(min_up_to(seq, 0) == seq[0] as int);
        if seq.len() == 1 {
            assert(min_iter_spec(seq, 0) == seq[0] as int);
        } else {
            lemma_min_up_to_extends(seq, seq.len() - 1);
        }
    } else {
        lemma_min_up_to_extends(seq, i - 1);
        assert(min_up_to(seq, i - 1) == min_iter_spec(seq, 0));
        lemma_min_up_to_monotone(seq, i - 1, i);
    }
}

proof fn lemma_max_up_to_monotone(seq: Seq<i32>, i: int, j: int)
    requires 0 <= i < j < seq.len()
    ensures max_up_to(seq, i) <= max_up_to(seq, j)
{
    /* code modified by LLM (iteration 5): prove monotonicity of max_up_to */
    if i == j - 1 {
        assert(max_up_to(seq, j) == max(seq[j] as int, max_up_to(seq, i)));
    } else {
        lemma_max_up_to_monotone(seq, i, j - 1);
    }
}

proof fn lemma_min_up_to_monotone(seq: Seq<i32>, i: int, j: int)
    requires 0 <= i < j < seq.len()
    ensures min_up_to(seq, i) >= min_up_to(seq, j)
{
    /* code modified by LLM (iteration 5): prove monotonicity of min_up_to */
    if i == j - 1 {
        assert(min_up_to(seq, j) == min(seq[j] as int, min_up_to(seq, i)));
    } else {
        lemma_min_up_to_monotone(seq, i, j - 1);
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    /* code modified by LLM (iteration 5): fixed loop invariants and bounds */
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            0 <= i - 1 < arr.len(),
            max_val as int == max_up_to(arr@, (i - 1) as int),
            min_val as int == min_up_to(arr@, (i - 1) as int),
            forall|j: int| 0 <= j < i ==> max_val >= arr[j],
            forall|j: int| 0 <= j < i ==> min_val <= arr[j],
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 5): added proof block for invariant maintenance */
        proof {
            assert(0 <= i < arr.len());
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
        /* code modified by LLM (iteration 5): fixed lemma calls and proof structure */
        assert(i == arr.len());
        assert(i - 1 == arr.len() - 1);
        lemma_max_up_to_extends(arr@, (arr.len() - 1) as int);
        lemma_min_up_to_extends(arr@, (arr.len() - 1) as int);
        lemma_max_rcur_equals_max_iter(arr@);
        lemma_min_rcur_equals_min_iter(arr@);
    }
    
    max_val - min_val
}
// </vc-code>

} // verus!

fn main() {}