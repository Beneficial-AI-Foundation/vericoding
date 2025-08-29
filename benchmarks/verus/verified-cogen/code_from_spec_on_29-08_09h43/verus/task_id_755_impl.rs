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

// <vc-helpers>
proof fn min_spec_property(seq: Seq<i32>)
    requires 0 < seq.len()
    ensures forall|i: int| 0 <= i < seq.len() ==> seq[i] >= min_spec(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
    } else {
        let later_min = min_spec(seq.drop_first());
        min_spec_property(seq.drop_first());
        if seq[0] <= later_min {
            assert forall|i: int| 1 <= i < seq.len() implies seq[i] >= later_min by {
                assert(seq.drop_first()[i - 1] == seq[i]);
            }
        } else {
            assert forall|i: int| 1 <= i < seq.len() implies seq[i] >= later_min by {
                assert(seq.drop_first()[i - 1] == seq[i]);
            }
        }
    }
}

proof fn min_spec_exists(seq: Seq<i32>)
    requires 0 < seq.len()
    ensures exists|i: int| 0 <= i < seq.len() && seq[i] == min_spec(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
        /* code modified by LLM (iteration 4): explicit witness for base case */
        assert(seq[0] == min_spec(seq));
    } else {
        let later_min = min_spec(seq.drop_first());
        min_spec_exists(seq.drop_first());
        if seq[0] <= later_min {
            /* code modified by LLM (iteration 4): witness is at index 0 */
            assert(seq[0] == min_spec(seq));
        } else {
            /* code modified by LLM (iteration 4): witness is from tail, shifted by 1 */
            assert(exists|i: int| 0 <= i < seq.drop_first().len() && seq.drop_first()[i] == later_min);
            let witness_idx_later = choose|i: int| 0 <= i < seq.drop_first().len() && seq.drop_first()[i] == later_min;
            let witness_idx = witness_idx_later + 1;
            assert(0 <= witness_idx < seq.len());
            assert(seq[witness_idx] == seq.drop_first()[witness_idx_later]);
            assert(seq[witness_idx] == later_min);
            assert(min_spec(seq) == later_min);
            assert(seq[witness_idx] == min_spec(seq));
        }
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut min_idx = 0;
    let mut second_min_idx = 1;
    
    /* code modified by LLM (iteration 4): handle initial case where indices might be swapped */
    if numbers[1] < numbers[0] {
        min_idx = 1;
        second_min_idx = 0;
    }
    
    for i in 2..numbers.len()
        invariant
            0 <= min_idx < numbers.len(),
            0 <= second_min_idx < numbers.len(),
            min_idx != second_min_idx,
            forall|k: int| 0 <= k < i ==> numbers[k] >= numbers[min_idx as int],
            forall|k: int| 0 <= k < i && k != min_idx ==> numbers[k] >= numbers[second_min_idx as int],
    {
        if numbers[i] < numbers[min_idx] {
            /* code modified by LLM (iteration 4): maintain distinct indices invariant */
            second_min_idx = min_idx;
            min_idx = i;
        } else if numbers[i] < numbers[second_min_idx] && i != min_idx {
            /* code modified by LLM (iteration 4): ensure we don't set second_min_idx to min_idx */
            second_min_idx = i;
        }
    }
    
    proof {
        /* code modified by LLM (iteration 4): establish postcondition using helper lemmas */
        min_spec_property(numbers@);
        min_spec_exists(numbers@);
        
        let min_val = min_spec(numbers@);
        assert(exists|k: int| 0 <= k < numbers.len() && numbers[k] == min_val);
        let witness_idx = choose|k: int| 0 <= k < numbers.len() && numbers[k] == min_val;
        
        assert(numbers[min_idx as int] <= numbers[witness_idx as int]);
        assert(numbers[witness_idx as int] == min_val);
        assert(numbers[min_idx as int] >= min_val) by {
            min_spec_property(numbers@);
        }
        assert(numbers[min_idx as int] == min_val);
        
        assert(0 <= second_min_idx < numbers.len());
        assert(second_min_idx != min_idx);
    }
    
    (min_idx, second_min_idx)
}
// </vc-code>

} // verus!

fn main() {}