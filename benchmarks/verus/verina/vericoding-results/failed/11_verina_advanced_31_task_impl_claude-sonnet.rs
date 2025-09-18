// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subsequence_of(subseq: Seq<i32>, seq: Seq<i32>) -> bool {
    exists|indices: Seq<int>| 
        indices.len() == subseq.len() &&
        #[trigger] indices.len() >= 0 &&
        (forall|i: int| 0 <= i < indices.len() ==> #[trigger] indices[i] >= 0 && indices[i] < seq.len()) &&
        (forall|i: int| 0 <= i < indices.len() - 1 ==> #[trigger] indices[i] < indices[i + 1]) &&
        (forall|i: int| 0 <= i < subseq.len() ==> #[trigger] subseq[i] == seq[indices[i]])
}

spec fn is_strictly_increasing(seq: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] seq[i] < seq[i + 1]
}
// </vc-preamble>

// <vc-helpers>
proof fn empty_subseq_is_increasing()
    ensures is_strictly_increasing(Seq::<i32>::empty())
{
}

proof fn single_element_is_increasing(x: i32)
    ensures is_strictly_increasing(seq![x])
{
}

/* helper modified by LLM (iteration 5): fixed type parameter to use i32 instead of generic T */
proof fn empty_is_subsequence_of_any(seq: Seq<i32>)
    ensures is_subsequence_of(Seq::<i32>::empty(), seq)
{
    let indices = Seq::<int>::empty();
    assert(indices.len() == 0);
    assert(Seq::<i32>::empty().len() == 0);
}

/* helper modified by LLM (iteration 5): fixed type parameter to use i32 instead of generic T */
proof fn subsequence_length_bound(subseq: Seq<i32>, seq: Seq<i32>)
    requires is_subsequence_of(subseq, seq)
    ensures subseq.len() <= seq.len()
{
}

/* helper modified by LLM (iteration 5): added decreases clause to recursive function */
fn compute_lis_length(xs: &Vec<i32>, memo: &mut Vec<Option<usize>>, i: usize) -> (result: usize)
    requires
        i < xs.len(),
        old(memo).len() == xs.len(),
    ensures
        result >= 1,
        exists|subseq: Seq<i32>|
            is_subsequence_of(subseq, xs@.subrange(i as int, xs.len() as int)) &&
            is_strictly_increasing(subseq) &&
            subseq.len() == result &&
            subseq[0] == xs@[i as int],
    decreases xs.len() - i
{
    if let Some(cached) = memo[i] {
        return cached;
    }
    
    let mut max_length = 1;
    let mut j = i + 1;
    
    while j < xs.len()
        invariant
            i < xs.len(),
            i + 1 <= j <= xs.len(),
            max_length >= 1,
        decreases xs.len() - j
    {
        if xs[j] > xs[i] {
            let length_from_j = compute_lis_length(xs, memo, j);
            if length_from_j + 1 > max_length {
                max_length = length_from_j + 1;
            }
        }
        j += 1;
    }
    
    memo.set(i, Some(max_length));
    max_length
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subseq_length(xs: &Vec<i32>) -> (result: usize)
    ensures

        exists|subseq: Seq<i32>| 
            is_subsequence_of(subseq, xs@) && 
            is_strictly_increasing(subseq) && 
            subseq.len() == result,

        forall|subseq: Seq<i32>| 
            (is_subsequence_of(subseq, xs@) && is_strictly_increasing(subseq)) 
            ==> subseq.len() <= result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    if xs.len() == 0 {
        proof {
            empty_is_subsequence_of_any(xs@);
            empty_subseq_is_increasing();
        }
        return 0;
    }
    
    let mut memo = Vec::with_capacity(xs.len());
    let mut k = 0;
    while k < xs.len()
        invariant
            k <= xs.len(),
            memo.len() == k,
        decreases xs.len() - k
    {
        memo.push(None);
        k += 1;
    }
    
    let mut max_length = 0;
    let mut i = 0;
    
    while i < xs.len()
        invariant
            i <= xs.len(),
            memo.len() == xs.len(),
            max_length >= 0,
        decreases xs.len() - i
    {
        let length_from_i = compute_lis_length(xs, &mut memo, i);
        if length_from_i > max_length {
            max_length = length_from_i;
        }
        i += 1;
    }
    
    max_length
}
// </vc-code>

}
fn main() {}