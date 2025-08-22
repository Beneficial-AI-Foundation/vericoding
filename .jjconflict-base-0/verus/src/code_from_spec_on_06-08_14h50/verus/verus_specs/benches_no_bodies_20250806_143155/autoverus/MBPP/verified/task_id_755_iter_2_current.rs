use vstd::prelude::*;
fn main() {
}

verus! {

spec fn min_spec(seq: Seq<i32>) -> int
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

// change the signatue to return -> (min_index, second_min_index)
fn second_smallest(numbers: &Vec<i32>) -> (indices: (
    usize,
    usize,
))  //(min_index, second_min_index)
    requires
        numbers.len()
            >= 2,  // There must be at least 2 different values, a minimum and another one

    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
{
    let mut min_idx = 0;
    let mut second_min_idx = 1;
    
    // Find the minimum index first
    let mut i = 1;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < numbers.len()
        invariant
            0 <= min_idx < numbers.len(),
            1 <= i <= numbers.len(),
            forall|j: int| 0 <= j < i ==> numbers[min_idx as int] <= numbers[j],
        decreases numbers.len() - i,
    {
        if numbers[i] < numbers[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    
    // Find second minimum index (smallest among non-minimum elements)
    if min_idx == 0 {
        second_min_idx = 1;
    } else {
        second_min_idx = 0;
    }
    
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while j < numbers.len()
        invariant
            0 <= min_idx < numbers.len(),
            0 <= second_min_idx < numbers.len(),
            0 <= j <= numbers.len(),
            min_idx != second_min_idx,
            forall|k: int| 0 <= k < numbers.len() ==> numbers[min_idx as int] <= numbers[k],
            forall|k: int| 0 <= k < j && k != min_idx ==> numbers[second_min_idx as int] <= numbers[k],
        decreases numbers.len() - j,
    {
        if j != min_idx {
            if numbers[j] < numbers[second_min_idx] {
                second_min_idx = j;
            }
        }
        j += 1;
    }
    
    (min_idx, second_min_idx)
}

} // verus!