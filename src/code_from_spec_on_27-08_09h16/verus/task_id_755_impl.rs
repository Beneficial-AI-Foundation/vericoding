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
spec fn min_index_spec(seq: Seq<i32>) -> int
    recommends 0 < seq.len()
    decreases seq.len()
{
    if seq.len() == 1 {
        0
    } else {
        let later_min_idx = min_index_spec(seq.drop_first());
        if seq[0] <= seq[later_min_idx + 1] {
            0
        } else {
            later_min_idx + 1
        }
    }
}

proof fn min_spec_correctness(seq: Seq<i32>)
    requires 0 < seq.len()
    ensures 
        min_spec(seq) == seq[min_index_spec(seq)],
        forall|i: int| 0 <= i < seq.len() ==> seq[i] >= min_spec(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(min_spec(seq) == seq[0] as int);
        assert(min_index_spec(seq) == 0);
        assert(seq[min_index_spec(seq)] == seq[0]);
    } else {
        min_spec_correctness(seq.drop_first());
        let later_min_idx = min_index_spec(seq.drop_first());
        assert(0 <= later_min_idx < seq.drop_first().len());
        
        if seq[0] <= seq[later_min_idx + 1] {
            assert(min_index_spec(seq) == 0);
            assert(min_spec(seq) == seq[0] as int);
            assert(seq[min_index_spec(seq)] == seq[0]);
        } else {
            assert(min_index_spec(seq) == later_min_idx + 1);
            assert(min_spec(seq) == seq[later_min_idx + 1] as int);
            assert(seq[min_index_spec(seq)] == seq[later_min_idx + 1]);
        }
    }
}

proof fn min_index_bounds(seq: Seq<i32>)
    requires 0 < seq.len()
    ensures 0 <= min_index_spec(seq) < seq.len()
    decreases seq.len()
{
    if seq.len() == 1 {
    } else {
        min_index_bounds(seq.drop_first());
    }
}
// </vc-helpers>

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
    
    for i in 1..numbers.len()
        invariant
            0 <= min_idx < numbers.len(),
            0 <= second_min_idx < numbers.len(),
            min_idx != second_min_idx,
            forall|k: int| 0 <= k < i ==> numbers[k] >= numbers[min_idx as int],
            forall|k: int| 0 <= k < i && k != min_idx ==> numbers[k] >= numbers[second_min_idx as int],
            i > min_idx ==> exists|k: int| 0 <= k < i && k != min_idx && numbers[k] == numbers[second_min_idx as int],
    {
        if numbers[i] < numbers[min_idx] {
            second_min_idx = min_idx;
            min_idx = i;
        } else if numbers[i] < numbers[second_min_idx] || second_min_idx == min_idx {
            second_min_idx = i;
        }
    }
    
    proof {
        min_spec_correctness(numbers@);
        min_index_bounds(numbers@);
        
        assert(min_idx == min_index_spec(numbers@));
        assert(forall|k: int| 0 <= k < numbers.len() ==> numbers[k] >= numbers[min_idx as int]);
        assert(numbers[min_idx as int] == min_spec(numbers@));
        assert(forall|k: int| 0 <= k < numbers.len() && k != min_idx ==> numbers[k] >= numbers[second_min_idx as int]);
        assert(exists|k: int| 0 <= k < numbers.len() && k != min_idx && numbers[k] == numbers[second_min_idx as int]);
    }
    
    (min_idx, second_min_idx)
}
// </vc-code>

} // verus!

fn main() {}