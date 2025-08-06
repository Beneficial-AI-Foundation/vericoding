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
// pure-end

fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))
    // pre-conditions-start
    requires
        numbers.len() >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
    // post-conditions-end
{
    let mut min_idx = 0;
    let mut second_min_idx = 1;
    
    // Find the minimum element first
    for i in 1..numbers.len()
        invariant
            min_idx < numbers.len(),
            forall|j: int| 0 <= j < i ==> numbers[min_idx as int] <= numbers[j],
    {
        if numbers[i] < numbers[min_idx] {
            min_idx = i;
        }
    }
    
    // Find the second minimum (smallest among non-minimum elements)
    if min_idx == 0 {
        second_min_idx = 1;
    } else {
        second_min_idx = 0;
    }
    
    for i in 0..numbers.len()
        invariant
            min_idx < numbers.len(),
            second_min_idx < numbers.len(),
            second_min_idx != min_idx,
            forall|j: int| 0 <= j < numbers.len() ==> numbers[min_idx as int] <= numbers[j],
            forall|j: int| 0 <= j < i && j != min_idx ==> numbers[second_min_idx as int] <= numbers[j],
    {
        if i != min_idx {
            if numbers[i] < numbers[second_min_idx] {
                second_min_idx = i;
            }
        }
    }
    
    (min_idx, second_min_idx)
}

} // verus!

fn main() {}