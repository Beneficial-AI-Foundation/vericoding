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
/* helper modified by LLM (iteration 5): fixed type annotation in second_smallest_exists proof function */
proof fn min_spec_correctness(seq: Seq<i32>, min_val: i32)
    requires
        seq.len() > 0,
        min_val as int == min_spec(seq),
    ensures
        exists|i: int| 0 <= i < seq.len() && seq[i] == min_val,
        forall|j: int| 0 <= j < seq.len() ==> seq[j] >= min_val,
{
    if seq.len() == 1 {
        assert(seq[0] == min_val);
    } else {
        let later_min = min_spec(seq.drop_first());
        min_spec_correctness(seq.drop_first(), later_min as i32);
        if seq[0] <= later_min {
            assert(seq[0] == min_val);
        } else {
            assert(later_min == min_val as int);
        }
    }
}

proof fn second_smallest_exists(numbers: &Vec<i32>, min_idx: usize)
    requires
        numbers.len() >= 2,
        0 <= min_idx < numbers.len(),
        numbers[min_idx as int] as int == min_spec(numbers@),
    ensures
        exists|i: int| 0 <= i < numbers.len() && i != min_idx && forall|j: int| 0 <= j < numbers.len() && j != min_idx ==> numbers[j] >= numbers[i],
{
    assert(numbers.len() >= 2);
    let second_idx: usize = if min_idx == 0 { 1 } else { 0 };
    assert(second_idx != min_idx);
    assert(0 <= second_idx < numbers.len());
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
{
    /* code modified by LLM (iteration 5): added explicit type annotation for second_idx */
    let mut min_idx = 0;
    let mut i = 1;
    
    while i < numbers.len()
        invariant
            0 <= min_idx < numbers.len(),
            1 <= i <= numbers.len(),
            forall|k: int| 0 <= k < i ==> numbers[k] >= numbers[min_idx as int],
    {
        if numbers[i] < numbers[min_idx] {
            min_idx = i;
        }
        i += 1usize;
    }
    
    proof {
        min_spec_correctness(numbers@, numbers[min_idx as int]);
    }
    
    let mut second_idx: usize = if min_idx == 0 { 1 } else { 0 };
    let mut j: usize = 0;
    
    while j < numbers.len()
        invariant
            0 <= j <= numbers.len(),
            0 <= second_idx < numbers.len(),
            second_idx != min_idx,
            forall|k: int| 0 <= k < j && k != min_idx ==> numbers[k] >= numbers[second_idx as int],
    {
        if j != min_idx && numbers[j] < numbers[second_idx] {
            second_idx = j;
        }
        j += 1usize;
    }
    
    proof {
        second_smallest_exists(numbers, min_idx);
    }
    
    (min_idx, second_idx)
}
// </vc-code>

}
fn main() {}