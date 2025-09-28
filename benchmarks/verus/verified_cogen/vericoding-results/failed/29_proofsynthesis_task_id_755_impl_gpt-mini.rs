// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min_spec(seq: Seq<i32>) -> (result: int)
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns index of minimum element in non-empty sequence */
spec fn index_of_min(seq: Seq<i32>) -> nat
    requires
        seq.len() > 0,
    decreases
        seq.len(),
    ensures
        result < seq.len(),
        seq[result as int] as int == min_spec(seq),
        forall|i: int| 0 <= i < seq.len() ==> seq[result as int] <= seq[i],
{
    if seq.len() == 1 {
        0
    } else {
        let tail_idx = index_of_min(seq.drop_first());
        let tail_idx_orig = tail_idx + 1;
        if seq[0] <= seq[tail_idx_orig as int] {
            0
        } else {
            tail_idx_orig
        }
    }
}

/* helper modified by LLM (iteration 5): returns index of minimum element excluding a given index */
spec fn index_of_min_excluding(seq: Seq<i32>, exclude: nat) -> nat
    requires
        seq.len() > 1,
        exclude < seq.len(),
    decreases
        seq.len(),
    ensures
        result < seq.len(),
        result != exclude,
        forall|i: int| 0 <= i < seq.len() && i != exclude as int ==> seq[result as int] <= seq[i],
{
    if seq.len() == 2 {
        if exclude == 0 { 1 } else { 0 }
    } else {
        if exclude == 0 {
            let tail_idx = index_of_min(seq.drop_first());
            tail_idx + 1
        } else {
            let tail_idx = index_of_min_excluding(seq.drop_first(), exclude - 1);
            let tail_idx_orig = tail_idx + 1;
            if seq[0] <= seq[tail_idx_orig as int] {
                0
            } else {
                tail_idx_orig
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))

    requires
        numbers.len() >= 2,

    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute indices of smallest and second-smallest */
{
    let mut min_i: usize = 0;
    let mut i: usize = 1;
    while i < numbers.len()
        invariant
            min_i < numbers.len(),
            forall|j: int| 0 <= j < i as int ==> numbers@[min_i as int] <= numbers@[j],
        decreases numbers.len() as int - i as int
    {
        if numbers[i] < numbers[min_i] {
            min_i = i;
        }
        i += 1;
    }

    let mut second_i: usize = if min_i == 0 { 1 } else { 0 };
    let mut k: usize = 0;
    while k < numbers.len()
        invariant
            k <= numbers.len(),
            second_i < numbers.len(),
            second_i != min_i,
            forall|t: int| 0 <= t < k as int && t != min_i as int ==> numbers@[second_i as int] <= numbers@[t],
        decreases numbers.len() as int - k as int
    {
        if k != min_i {
            if numbers[k] < numbers[second_i] {
                second_i = k;
            }
        }
        k += 1;
    }

    (min_i, second_i)
}
// </vc-code>

}
fn main() {}