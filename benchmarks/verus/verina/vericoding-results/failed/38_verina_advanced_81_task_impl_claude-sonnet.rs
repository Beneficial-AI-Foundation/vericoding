// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sorted_insert(sorted_vec: &mut Vec<i32>, value: i32)
    requires
        old(sorted_vec).len() < usize::MAX,
        forall|i: int| 0 <= i < old(sorted_vec).len() - 1 ==> old(sorted_vec)[i] <= old(sorted_vec)[i + 1],
    ensures
        sorted_vec.len() == old(sorted_vec).len() + 1,
        forall|i: int| 0 <= i < sorted_vec.len() - 1 ==> sorted_vec[i] <= sorted_vec[i + 1],
        sorted_vec@.contains(value),
        forall|x: i32| x != value ==> (old(sorted_vec)@.contains(x) <==> sorted_vec@.contains(x)),
{
    let mut pos = 0;
    while pos < sorted_vec.len()
        invariant
            0 <= pos <= sorted_vec.len(),
            forall|i: int| 0 <= i < pos ==> sorted_vec[i] < value,
            sorted_vec.len() == old(sorted_vec).len(),
            forall|i: int| 0 <= i < sorted_vec.len() - 1 ==> sorted_vec[i] <= sorted_vec[i + 1],
    {
        if sorted_vec[pos] >= value {
            break;
        }
        pos += 1;
    }
    sorted_vec.insert(pos, value);
}

/* helper modified by LLM (iteration 5): Fix type mismatch in subrange call */
spec fn count_occurrences(seq: Seq<i32>, value: i32) -> nat
{
    if seq.len() == 0 {
        0
    } else {
        let head_count: nat = if seq[0] == value { 1 } else { 0 };
        head_count + count_occurrences(seq.subrange(1, seq.len() as int), value)
    }
}
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplify by removing count_occurrences usage */
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..arr.len()
        invariant
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() - 1 ==> result[j] <= result[j + 1],
            forall|x: i32| result@.contains(x) ==> arr@.subrange(0, i as int).contains(x),
            forall|x: i32| arr@.subrange(0, i as int).contains(x) ==> result@.contains(x),
    {
        let current = arr[i];
        if !result@.contains(current) {
            sorted_insert(&mut result, current);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}