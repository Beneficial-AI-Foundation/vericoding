use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
proof fn lemma_subrange_extend(numbers: Seq<int>, i: int)
    requires
        0 <= i < numbers.len() - 1,
    ensures
        numbers.subrange(0, i + 1).push(numbers[i + 1]) == numbers.subrange(0, i + 2),
{
}

proof fn lemma_max_in_extended_range(numbers: Seq<int>, max_so_far: int, i: int)
    requires
        0 <= i < numbers.len() - 1,
        isMax(max_so_far, numbers.subrange(0, i + 1)),
    ensures
        isMax(if max_so_far >= numbers[i + 1] { max_so_far } else { numbers[i + 1] }, 
              numbers.subrange(0, i + 2)),
{
    let new_max = if max_so_far >= numbers[i + 1] { max_so_far } else { numbers[i + 1] };
    let old_range = numbers.subrange(0, i + 1);
    let new_range = numbers.subrange(0, i + 2);
    
    // Prove new_max is in new_range
    if max_so_far >= numbers[i + 1] {
        // new_max == max_so_far, which is in old_range, which is part of new_range
        assert(old_range.contains(max_so_far));
        assert(forall|j: int| 0 <= j < old_range.len() ==> old_range[j] == new_range[j]);
        assert(new_range.contains(new_max));
    } else {
        // new_max == numbers[i + 1], which is the last element of new_range
        assert(new_range[new_range.len() - 1] == numbers[i + 1]);
        assert(new_range.contains(new_max));
    }
    
    // Prove all elements in new_range are <= new_max
    assert(forall|j: int| 0 <= j < new_range.len() ==> new_range[j] <= new_max) by {
        assert(forall|j: int| 0 <= j < old_range.len() ==> old_range[j] <= max_so_far);
        assert(new_range.len() == old_range.len() + 1);
        assert(new_range[new_range.len() - 1] == numbers[i + 1]);
        
        let k = arbitrary::<int>();
        if 0 <= k < new_range.len() {
            if k < old_range.len() {
                assert(new_range[k] == old_range[k]);
                assert(old_range[k] <= max_so_far);
                assert(new_range[k] <= new_max);
            } else {
                assert(k == new_range.len() - 1);
                assert(new_range[k] == numbers[i + 1]);
                assert(new_range[k] <= new_max);
            }
        }
    };
}

proof fn lemma_first_element_is_max(numbers: Seq<int>)
    requires
        numbers.len() > 0,
    ensures
        isMax(numbers[0], numbers.subrange(0, 1)),
{
    let subseq = numbers.subrange(0, 1);
    assert(subseq.len() == 1);
    assert(subseq[0] == numbers[0]);
    assert(subseq.contains(numbers[0]));
    assert(forall|i: int| 0 <= i < subseq.len() ==> subseq[i] <= numbers[0]) by {
        let j = arbitrary::<int>();
        if 0 <= j < subseq.len() {
            assert(j == 0);
            assert(subseq[j] == numbers[0]);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push(numbers[0]);
    
    proof {
        lemma_first_element_is_max(numbers@);
    }
    
    let mut i = 1;
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            result.len() == i,
            result[0] == numbers[0],
            forall|j: int| 0 < j < result.len() ==> isMax(result[j], numbers@.subrange(0, j + 1)),
        decreases numbers.len() - i,
    {
        let max_so_far = result[i - 1];
        let new_max = if max_so_far >= numbers[i] { max_so_far } else { numbers[i] };
        result.push(new_max);
        
        proof {
            assert(0 <= (i - 1) as int < numbers@.len() - 1);
            assert(isMax(max_so_far, numbers@.subrange(0, (i - 1) as int + 1)));
            lemma_max_in_extended_range(numbers@, max_so_far, (i - 1) as int);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}