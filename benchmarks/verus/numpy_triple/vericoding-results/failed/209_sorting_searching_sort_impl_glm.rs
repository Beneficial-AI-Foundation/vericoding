// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
}

/* helper modified by LLM (iteration 2): fixed type parameter to use i32 */
proof fn lemma_count_occurrences_append(seq1: Seq<i32>, seq2: Seq<i32>, x: i32)
    ensures
        count_occurrences(seq1 + seq2, x) == count_occurrences(seq1, x) + count_occurrences(seq2, x),
{
    if seq1.len() == 0 {
        assert(seq1 + seq2 == seq2);
    } else {
        lemma_count_occurrences_append(seq1.skip(1), seq2, x);
        assert((seq1 + seq2).skip(1) == seq1.skip(1) + seq2);
    }
}

/* helper modified by LLM (iteration 3): fixed integer literal types */
proof fn lemma_count_occurrences_singleton(x: i32, y: i32)
    ensures
        count_occurrences(Seq::new(1, |i: int| if i == 0 { x } else { y }), y) == (if x == y { 1int } else { 0int }),
{
    assert(Seq::new(1, |i: int| if i == 0 { x } else { y })[0] == x);
}

/* helper modified by LLM (iteration 5): replaced split_at with subrange and to_vec */
fn merge_sort_impl(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        is_sorted(result@),
        forall|x: i32| count_occurrences(result@, x) == count_occurrences(arr@, x),
{
    if arr.len() <= 1 {
        arr.clone()
    } else {
        let mid = arr.len() / 2;
        let left = arr@.subrange(0, mid as int).to_vec();
        let right = arr@.subrange(mid as int, arr.len() as int).to_vec();
        let sorted_left = merge_sort_impl(&left);
        let sorted_right = merge_sort_impl(&right);
        merge(&sorted_left, &sorted_right)
    }
}

fn merge(left: &Vec<i32>, right: &Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(left@),
        is_sorted(right@),
    ensures
        result.len() == left.len() + right.len(),
        is_sorted(result@),
        forall|x: i32| count_occurrences(result@, x) == count_occurrences(left@, x) + count_occurrences(right@, x),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() || j < right.len()
        invariant
            i <= left.len(),
            j <= right.len(),
            result.len() == i + j,
            forall|k: int| 0 <= k < i ==> left@[k] <= left@[i - 1],
            forall|k: int| 0 <= k < j ==> right@[k] <= right@[j - 1],
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result@[k] <= result@[l],
            forall|x: i32| count_occurrences(result@, x) == count_occurrences(left@.subrange(0, i as int), x) + count_occurrences(right@.subrange(0, j as int), x),
        decreases (left.len() - i) + (right.len() - j),
    {
        if i < left.len() && (j >= right.len() || left[i] <= right[j]) {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(seq: Seq<i32>, x: i32) -> int
    decreases seq.len()
{
    if seq.len() == 0 {
        0int
    } else {
        (if seq[0] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1), x)
    }
}

fn sort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using fixed merge_sort_impl without split_at */
    let result = merge_sort_impl(&a);
    result
}
// </vc-code>


}
fn main() {}