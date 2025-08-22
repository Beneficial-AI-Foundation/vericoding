use vstd::prelude::*;
fn main() {}

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
{
    /* code modified by LLM (iteration 1): Added decreases clauses to fix compilation error */
    let mut min_idx: usize = 0;
    let mut second_min_idx: usize = 1;
    
    // Find the minimum element first
    let mut i = 1;
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
    
    // Find the second minimum element
    if min_idx == 0 {
        second_min_idx = 1;
    } else {
        second_min_idx = 0;
    }
    
    i = 0;
    while i < numbers.len()
        invariant
            0 <= min_idx < numbers.len(),
            0 <= second_min_idx < numbers.len(),
            min_idx != second_min_idx,
            0 <= i <= numbers.len(),
            forall|j: int| 0 <= j < numbers.len() ==> numbers[min_idx as int] <= numbers[j],
            forall|j: int| 0 <= j < i && j != min_idx ==> numbers[second_min_idx as int] <= numbers[j],
        decreases numbers.len() - i,
    {
        if i != min_idx && numbers[i] < numbers[second_min_idx] {
            second_min_idx = i;
        }
        i += 1;
    }
    
    (min_idx, second_min_idx)
}

} // verus!