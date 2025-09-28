// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn distinct_in_range(seq: Seq<i8>, low: int, high: int)
    requires
        low <= high,
        forall|i: int, j: int| low <= i < j < high ==> seq[i] <= seq[j]
    ensures
        forall|i: int, j: int| low <= i < j < high ==> seq[i] < seq[j]
{
    if low < high {
        dist_range_inner(seq, low, high);
    }
}

proof fn dist_range_inner(seq: Seq<i8>, i: int, high: int)
    requires
        i < high,
        forall|k: int, l: int| i <= k < l < high ==> seq[k] <= seq[l]
    ensures
        forall|k: int, l: int| i <= k < l < high ==> seq[k] < seq[l]
    decreases high - i
{
    assert(seq[i] <= seq[i + 1]);
    assert(i + 1 < high ==> seq[i] <= seq[i + 1] < seq[i + 2] || !(i + 2 < high));
    if i + 1 < high {
        dist_range_inner(seq, i + 1, high);
    }
}

fn dedup_sorted(seq: Seq<i8>) -> (result: Seq<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> seq.contains(x),
        forall|x: i8| seq.contains(x) ==> result@.contains(x)
{
    if seq.len() == 0 {
        Seq::empty()
    } else {
        let mut result: Seq<i8> = Seq::empty();
        let mut i: int = 0;
        while i < seq.len()
            invariant
                0 <= i <= seq.len(),
                result@.len() >= 0,
                forall|x: i8| result@.contains(x) ==> seq.contains(x),
                forall|x: i8| !(seq.subrange(0, i).contains(x)) && seq.contains(x) ==> result@.contains(x),
                i > 0 ==> result@.len() > 0,
                forall|k: int, l: int| 0 <= k < l < result@.len() ==> result@[k] < result@[l]
        {
            if i == 0 || seq[i] != seq[i - 1] {
                result = result.push(seq[i]);
            }
            i = i + 1;
        }
        assert(forall|x: i8| seq.contains(x) ==> result@.contains(x));
        result
    }
}

fn sort_seq(seq: Seq<i8>) -> (result: Seq<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j],
        forall|x: i8| result@.contains(x) == seq.contains(x)
{
    if seq.len() <= 1 {
        seq
    } else {
        let pivot_idx = seq.len() / 2;
        let pivot = seq[pivot_idx];
        let (left, right) = seq.partition(|x| x <= pivot);
        let sorted_left = sort_seq(left);
        let sorted_right = sort_seq(right);
        sorted_left.append(sorted_right)
    }
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i8>) -> (result: Vec<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int) &&
        forall|x: i8| result@.contains(x) ==> s@.contains(x) &&
        forall|x: i8| s@.contains(x) ==> result@.contains(x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed subrange syntax error and simplified implementation */
    let seq = s@;
    let sorted = sort_seq(seq);
    distinct_in_range(sorted, 0, sorted.len());
    let result_seq = dedup_sorted(sorted);
    let result_vec = Vec::<i8>::from_seq(result_seq);
    result_vec
}
// </vc-code>


}

fn main() {}