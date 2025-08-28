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
spec fn seq_without_index(seq: Seq<i32>, idx: int) -> Seq<i32>
    recommends 0 <= idx < seq.len()
{
    seq.subrange(0, idx) + seq.subrange(idx + 1, seq.len() as int)
}

spec fn min_excluding_index(seq: Seq<i32>, exclude_idx: int) -> int
    recommends 
        0 <= exclude_idx < seq.len(),
        seq.len() >= 2,
{
    min_spec(seq_without_index(seq, exclude_idx))
}

proof fn lemma_min_is_in_seq(seq: Seq<i32>)
    requires seq.len() > 0
    ensures exists|i: int| 0 <= i < seq.len() && seq[i] == min_spec(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(seq[0] == min_spec(seq));
    } else {
        lemma_min_is_in_seq(seq.drop_first());
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            assert(seq[0] == min_spec(seq));
        } else {
            assert(exists|i: int| 1 <= i < seq.len() && seq[i] == later_min);
        }
    }
}

proof fn lemma_min_is_smallest(seq: Seq<i32>)
    requires seq.len() > 0
    ensures forall|i: int| 0 <= i < seq.len() ==> seq[i] >= min_spec(seq)
    decreases seq.len()
{
    if seq.len() == 1 {
        assert(seq[0] == min_spec(seq));
    } else {
        lemma_min_is_smallest(seq.drop_first());
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            assert(forall|i: int| 1 <= i < seq.len() ==> seq[i] >= later_min);
            assert(forall|i: int| 1 <= i < seq.len() ==> seq[i] >= seq[0]);
        } else {
            assert(forall|i: int| 1 <= i < seq.len() ==> seq[i] >= later_min);
            assert(seq[0] >= later_min);
        }
    }
}

proof fn lemma_seq_without_index_properties(seq: Seq<i32>, idx: int)
    requires 0 <= idx < seq.len()
    requires seq.len() >= 1
    ensures seq_without_index(seq, idx).len() == seq.len() - 1
    ensures forall|i: int| 0 <= i < idx ==> seq_without_index(seq, idx)[i] == seq[i]
    ensures forall|i: int| idx < i < seq.len() ==> seq_without_index(seq, idx)[i-1] == seq[i]
{
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
    let mut i = 1;
    
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            0 <= min_idx < i,
            forall|k: int| 0 <= k < i ==> numbers[k] >= numbers[min_idx as int],
    {
        if numbers[i] < numbers[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    
    proof {
        lemma_min_is_in_seq(numbers@);
        lemma_min_is_smallest(numbers@);
        assert(numbers[min_idx as int] == min_spec(numbers@));
    }
    
    let mut second_min_idx = if min_idx == 0 { 1 } else { 0 };
    i = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            0 <= second_min_idx < numbers.len(),
            second_min_idx != min_idx,
            forall|k: int| 0 <= k < i && k != min_idx ==> numbers[k] >= numbers[second_min_idx as int],
    {
        if i != min_idx && numbers[i] < numbers[second_min_idx] {
            second_min_idx = i;
        }
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k < numbers.len() && k != min_idx ==> numbers[k] >= numbers[second_min_idx as int]);
        assert(exists|k: int| 0 <= k < numbers.len() && k != min_idx && numbers[k] == numbers[second_min_idx as int]) by {
            assert(0 <= second_min_idx < numbers.len() && second_min_idx != min_idx && numbers[second_min_idx as int] == numbers[second_min_idx as int]);
        }
    }
    
    (min_idx, second_min_idx)
}
// </vc-code>

} // verus!

fn main() {}