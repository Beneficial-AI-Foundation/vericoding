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
    assert(isMax(current_max, numbers.subrange(0, 1))) by {
        let subseq = numbers.subrange(0, 1);
        assert(subseq.len() == 1);
        assert(subseq.spec_index(0) == numbers.spec_index(0));
        assert(subseq.spec_index(0) == current_max);
    }
    
    let mut idx: usize = 1;
    while idx < numbers.len()
        invariant
            1 <= idx <= numbers.len(),
            result_vec.len() == idx,
            forall|i: int| 0 <= i < result_vec.len() ==> isMax(result_vec.spec_index(i), numbers.subrange(0, i+1)),
            current_max == result_vec.spec_index((idx-1) as int)
    {
        let current_num = numbers.spec_index(idx as int);
        
        let old_max = current_max;
        if current_num > current_max {
            current_max = current_num;
        }
        
        // Prove that current_max is the maximum in subrange [0, idx+1)
        let subseq = numbers.subrange(0, (idx+1) as int);
        
        // Prove current_max appears in the subsequence
        assert(exists|k: int| 0 <= k < subseq.len() && subseq.spec_index(k) == current_max) by {
            if current_max == current_num {
                // current_max is the new number at position idx
                assert(subseq.spec_index(idx as int) == current_max);
            } else {
                // current_max didn't change, so it was the max of previous elements
                assert(current_max == old_max);
                let prev_subseq = numbers.subrange(0, idx as int);
                assert(isMax(current_max, prev_subseq));
                // Find the position where current_max appears in prev_subseq
                assert(exists|k: int| 0 <= k < prev_subseq.len() && prev_subseq.spec_index(k) == current_max);
                // This position is also valid in the extended subsequence
                assert(forall|k: int| 0 <= k < idx ==> subseq.spec_index(k) == prev_subseq.spec_index(k));
            }
        }
        
        // Prove current_max is >= all elements in the subsequence
        assert(forall|j: int| 0 <= j < subseq.len() ==> subseq.spec_index(j) <= current_max) by {
            let prev_subseq = numbers.subrange(0, idx as int);
            assert(isMax(old_max, prev_subseq));
            assert(forall|j: int| 0 <= j < prev_subseq.len() ==> prev_subseq.spec_index(j) <= old_max);
            assert(forall|j: int| 0 <= j < idx ==> subseq.spec_index(j) == prev_subseq.spec_index(j));
            assert(subseq.spec_index(idx as int) == current_num);
            assert(current_max >= old_max);
            assert(current_max >= current_num);
        }
        
        // Conclude that isMax holds
        assert(subseq.len() > 0);
        assert(isMax(current_max, subseq));
        
        result_vec.push(current_max);
        idx = idx + 1;
    }
    
    result_vec.view()
}

}