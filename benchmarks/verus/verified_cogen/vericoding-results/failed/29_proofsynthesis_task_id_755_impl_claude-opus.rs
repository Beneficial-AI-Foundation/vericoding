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
proof fn min_spec_in_seq(seq: Seq<i32>)
    requires
        0 < seq.len(),
    ensures
        exists|i: int| 0 <= i < seq.len() && seq[i] == min_spec(seq),
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(seq[0] == min_spec(seq));
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            assert(seq[0] == min_spec(seq));
        } else {
            min_spec_in_seq(seq.drop_first());
            let j = choose|j: int| 1 <= j < seq.len() && seq[j] == later_min;
            assert(seq[j] == min_spec(seq));
        }
    }
}

/* helper modified by LLM (iteration 5): Simplified proof structure for min_val_is_min_spec */
proof fn min_val_is_min_spec(numbers: &Vec<i32>, min_idx: usize, min_val: i32)
    requires
        numbers.len() >= 2,
        0 <= min_idx < numbers.len(),
        min_val == numbers[min_idx as int],
        forall|k: int| 0 <= k < numbers.len() ==> numbers[k] >= min_val,
    ensures
        min_val == min_spec(numbers@),
    decreases numbers.len(),
{
    if numbers.len() == 2 {
        assert(numbers[0] >= min_val);
        assert(numbers[1] >= min_val);
        if numbers[0] <= numbers[1] {
            if min_idx == 0 {
                assert(min_val == numbers[0]);
                assert(min_spec(numbers@) == numbers[0] as int);
            } else {
                assert(min_idx == 1);
                assert(min_val == numbers[1]);
                assert(numbers[0] >= numbers[1]);
                assert(numbers[0] == numbers[1]);
                assert(min_spec(numbers@) == numbers[0] as int);
                assert(min_val == numbers[0] as int);
            }
        } else {
            assert(numbers[1] < numbers[0]);
            if min_idx == 1 {
                assert(min_val == numbers[1]);
                assert(min_spec(numbers@) == numbers[1] as int);
            } else {
                assert(min_idx == 0);
                assert(min_val == numbers[0]);
                assert(numbers[1] >= numbers[0]);
                assert(false);
            }
        }
    } else {
        let later_min = min_spec(numbers@.drop_first());
        if numbers[0] <= later_min {
            assert(numbers[0] >= min_val);
            if min_idx == 0 {
                assert(min_val == numbers[0]);
                assert(min_spec(numbers@) == numbers[0] as int);
            } else {
                assert(min_idx >= 1);
                min_spec_in_seq(numbers@.drop_first());
                let j = choose|j: int| 1 <= j < numbers.len() && numbers[j] == later_min;
                assert(numbers[j] >= min_val);
                assert(later_min >= min_val);
                assert(numbers[0] >= min_val);
                assert(min_val <= numbers[0]);
                assert(min_val <= later_min);
                assert(min_val == numbers[0] as int);
                assert(min_spec(numbers@) == numbers[0] as int);
            }
        } else {
            assert(numbers[0] > later_min);
            assert(min_spec(numbers@) == later_min);
            min_spec_in_seq(numbers@.drop_first());
            let j = choose|j: int| 1 <= j < numbers.len() && numbers[j] == later_min;
            assert(numbers[j] == later_min);
            assert(numbers[j] >= min_val);
            assert(later_min >= min_val);
            assert(min_val <= later_min);
            assert(min_val == later_min as int);
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
{
    /* code modified by LLM (iteration 5): Fixed implementation and proof call */
    let mut min_idx: usize = 0;
    let mut min_val = numbers[0];
    let mut second_min_idx: usize = 1;
    let mut second_min_val = numbers[1];
    
    if min_val > second_min_val {
        min_idx = 1;
        min_val = numbers[1];
        second_min_idx = 0;
        second_min_val = numbers[0];
    }
    
    let mut i: usize = 2;
    while i < numbers.len()
        invariant
            2 <= i <= numbers.len(),
            0 <= min_idx < i,
            0 <= second_min_idx < i,
            min_idx != second_min_idx,
            min_val == numbers[min_idx as int],
            second_min_val == numbers[second_min_idx as int],
            forall|k: int| 0 <= k < i ==> numbers[k] >= min_val,
            forall|k: int| 0 <= k < i && k != min_idx ==> numbers[k] >= second_min_val,
            min_val <= second_min_val,
        decreases numbers.len() - i
    {
        if numbers[i] < min_val {
            second_min_idx = min_idx;
            second_min_val = min_val;
            min_idx = i;
            min_val = numbers[i];
        } else if numbers[i] < second_min_val {
            second_min_idx = i;
            second_min_val = numbers[i];
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k < numbers.len() ==> numbers[k] >= min_val);
        min_val_is_min_spec(numbers, min_idx, min_val);
        assert(min_val == min_spec(numbers@));
        assert(numbers[min_idx as int] == min_spec(numbers@));
    }
    
    (min_idx, second_min_idx)
}
// </vc-code>

}
fn main() {}