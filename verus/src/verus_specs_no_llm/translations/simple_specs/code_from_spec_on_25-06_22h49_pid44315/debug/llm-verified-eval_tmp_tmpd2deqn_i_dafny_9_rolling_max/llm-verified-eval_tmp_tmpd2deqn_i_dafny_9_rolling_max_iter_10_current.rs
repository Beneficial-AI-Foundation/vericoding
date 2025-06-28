use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isMax(max_val: int, seq: Seq<int>) -> bool {
    seq.len() > 0 && 
    (exists|i: int| 0 <= i < seq.len() && seq.spec_index(i) == max_val) &&
    (forall|j: int| 0 <= j < seq.len() ==> seq.spec_index(j) <= max_val)
}

fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires
        numbers.len() > 0
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < result.len() ==> isMax(result.spec_index(i), numbers.subrange(0, i+1))
{
    let mut result_vec: Vec<int> = Vec::new();
    let mut current_max = numbers.spec_index(0);
    result_vec.push(current_max);
    
    // Prove the base case
    assert(isMax(current_max, numbers.subrange(0, 1)));
    
    let mut idx: usize = 1;
    while idx < numbers.len()
        invariant
            1 <= idx <= numbers.len(),
            result_vec.len() == idx,
            forall|i: int| 0 <= i < result_vec.len() ==> isMax(result_vec.spec_index(i), numbers.subrange(0, i+1)),
            current_max == result_vec.spec_index((idx as int) - 1)
    {
        let current_num = numbers.spec_index(idx as int);
        
        let old_max = current_max;
        if current_num > current_max {
            current_max = current_num;
        }
        
        // Prove that current_max is the maximum in subrange [0, idx+1)
        let subseq = numbers.subrange(0, (idx as int) + 1);
        let prev_subseq = numbers.subrange(0, idx as int);
        
        // Key insight: subrange properties
        assert(subseq.len() == (idx as int) + 1);
        assert(prev_subseq.len() == idx as int);
        assert(forall|k: int| 0 <= k < (idx as int) ==> subseq.spec_index(k) == prev_subseq.spec_index(k));
        assert(subseq.spec_index(idx as int) == current_num);
        
        // Prove current_max appears in the subsequence
        if current_max == current_num {
            assert(subseq.spec_index(idx as int) == current_max);
        } else {
            assert(current_max == old_max);
            // Since old_max was max of prev_subseq, it appears there
            assert(exists|k: int| 0 <= k < prev_subseq.len() && prev_subseq.spec_index(k) == current_max);
            // And that position is still valid in subseq
            assert(exists|k: int| 0 <= k < subseq.len() && subseq.spec_index(k) == current_max);
        }
        
        // Prove current_max is >= all elements in the subsequence
        assert(forall|j: int| 0 <= j < prev_subseq.len() ==> prev_subseq.spec_index(j) <= old_max);
        assert(current_max >= old_max);
        assert(current_max >= current_num);
        assert(forall|j: int| 0 <= j < subseq.len() ==> subseq.spec_index(j) <= current_max);
        
        // Conclude that isMax holds
        assert(isMax(current_max, subseq));
        
        result_vec.push(current_max);
        idx = idx + 1;
    }
    
    result_vec.view()
}

}