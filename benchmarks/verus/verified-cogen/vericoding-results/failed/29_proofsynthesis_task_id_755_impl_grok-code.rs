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
/* helper modified by LLM (iteration 5): fixed nested proof block issue by removing inner proof block in initialization */
fn find_min_index(numbers: &Vec<i32>) -> (index: usize)
    requires
        numbers.len() > 0
    ensures
        0 <= index < numbers.len(),
        forall|j: int| 0 <= j < numbers.len() ==> numbers@[index as int] <= numbers@[j],
        numbers@[index as int] == min_spec(numbers@)
{
    let mut min_idx = 0;
    proof {
        assert(0 <= min_idx < numbers.len());
    }
    for i in 1..numbers.len()
        invariant
            0 <= i <= numbers.len(),
            0 <= min_idx < numbers.len(),
            forall|j: int| 0 <= j < i ==> numbers@[min_idx as int] <= numbers@[j]
    {
        proof { assert(i < numbers@.len()); }
        if numbers[i] < numbers[min_idx] {
            min_idx = i;
        }
        proof { assert(0 <= min_idx < numbers.len()); }
    }
    proof {
        assert(0 <= min_idx < numbers.len());
        assert(numbers@[min_idx as int] == min_spec(numbers@));
    }
    min_idx
}

/* helper modified by LLM (iteration 5): removed nested proof block to fix compilation error */
fn find_min_index_excluding(numbers: &Vec<i32>, excluded: usize) -> (index: usize)
    requires
        numbers.len() > 1,
        0 <= excluded < numbers.len()
    ensures
        0 <= index < numbers.len(),
        index != excluded,
        forall|j: int| 0 <= j < numbers.len() && j != excluded as int ==> numbers@[index as int] <= numbers@[j]
{
    let mut min_idx = if 0 != excluded { 0 } else { 1 };
    proof {
        assert(0 <= min_idx < numbers.len());
        if 0 != excluded {
            assert(min_idx == 0);
            assert(0 != excluded);
        } else {
            assert(min_idx == 1);
            assert(1 <= min_idx < numbers.len());
        }
    }
    for i in 0..numbers.len()
        invariant
            0 <= i <= numbers.len(),
            0 <= min_idx < numbers.len(),
            min_idx != excluded as int,
            forall|j: int| 0 <= j < i && j != excluded as int ==> numbers@[min_idx as int] <= numbers@[j]
        decreases (numbers.len() - i) as nat
    {
        proof { assert(i < numbers@.len()); }
        if i != excluded && numbers[i] < numbers[min_idx] {
            min_idx = i;
            proof { assert(min_idx != excluded as int); }
        }
    }
    proof {
        assert(0 <= min_idx < numbers.len());
        assert(min_idx != excluded);
    }
    min_idx
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
/* code modified by LLM (iteration 5): implemented second_smallest using helper functions, removed verification bypasses */
{
    let min_idx = find_min_index(numbers);
    let second_idx = find_min_index_excluding(numbers, min_idx);
    proof {
        assert(0 <= min_idx < numbers.len());
        assert(0 <= second_idx < numbers.len());
        assert(second_idx != min_idx);
        assert(numbers@[min_idx as int] == min_spec(numbers@));
        assert(exists|k: int| 0 <= k < numbers.len() && k != min_idx && numbers@[k] == numbers@[second_idx as int]);
    }
    (min_idx, second_idx)
}
// </vc-code>

}
fn main() {}