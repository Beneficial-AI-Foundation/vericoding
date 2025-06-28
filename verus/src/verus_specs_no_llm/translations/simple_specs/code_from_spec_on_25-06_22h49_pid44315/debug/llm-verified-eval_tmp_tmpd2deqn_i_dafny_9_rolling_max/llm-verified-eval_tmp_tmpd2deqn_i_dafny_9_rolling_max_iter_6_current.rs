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
    let mut result: Seq<int> = Seq::empty();
    let mut current_max = numbers.spec_index(0);
    result = result.push(current_max);
    
    // Prove the base case
    assert(result.len() == 1);
    assert(numbers.subrange(0, 1).len() == 1);
    assert(numbers.subrange(0, 1).spec_index(0) == numbers.spec_index(0));
    assert(current_max == numbers.spec_index(0));
    
    // Prove isMax for base case
    assert(numbers.subrange(0, 1).len() > 0);
    assert(numbers.subrange(0, 1).spec_index(0) == current_max);
    assert(forall|j: int| 0 <= j < numbers.subrange(0, 1).len() ==> numbers.subrange(0, 1).spec_index(j) <= current_max) by {
        assert(numbers.subrange(0, 1).len() == 1);
        assert(numbers.subrange(0, 1).spec_index(0) <= current_max);
    };
    assert(exists|k: int| 0 <= k < numbers.subrange(0, 1).len() && numbers.subrange(0, 1).spec_index(k) == current_max) by {
        assert(numbers.subrange(0, 1).spec_index(0) == current_max);
    };
    assert(isMax(result.spec_index(0), numbers.subrange(0, 1)));
    
    let mut idx: usize = 1;
    while idx < numbers.len()
        invariant
            1 <= idx <= numbers.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < result.len() ==> isMax(result.spec_index(i), numbers.subrange(0, i+1)),
            current_max == result.spec_index((idx-1) as int)
    {
        let current_num = numbers.spec_index(idx as int);
        
        if current_num > current_max {
            current_max = current_num;
        }
        
        // Prove that current_max is indeed the maximum in subrange [0, idx+1)
        let subseq = numbers.subrange(0, (idx+1) as int);
        
        // Prove current_max appears in the subsequence
        assert(exists|k: int| 0 <= k < subseq.len() && subseq.spec_index(k) == current_max) by {
            if current_max == current_num {
                assert(subseq.spec_index(idx as int) == current_max);
            } else {
                // current_max didn't change, so it was the max of previous elements
                assert(current_max >= current_num);
                assert(isMax(current_max, numbers.subrange(0, idx as int)));
                // From isMax, we know current_max exists in the previous subrange
                assert(exists|k: int| 0 <= k < idx && numbers.spec_index(k) == current_max);
                // And the previous subrange is a prefix of the current one
                assert(forall|k: int| 0 <= k < idx ==> subseq.spec_index(k) == numbers.spec_index(k));
            }
        };
        
        // Prove current_max is >= all elements in the subsequence
        assert(forall|j: int| 0 <= j < subseq.len() ==> subseq.spec_index(j) <= current_max) by {
            assert(forall|j: int| 0 <= j < idx ==> numbers.spec_index(j) <= current_max) by {
                if current_max == current_num {
                    // Previous max was <= current_num, and all previous elements were <= previous max
                    assert(forall|j: int| 0 <= j < idx ==> numbers.spec_index(j) <= result.spec_index((idx-1) as int));
                    assert(result.spec_index((idx-1) as int) <= current_num);
                } else {
                    // current_max unchanged, so it was already max of previous elements
                    assert(isMax(current_max, numbers.subrange(0, idx as int)));
                }
            };
            assert(current_max >= current_num);
            // All elements in subseq are either from the previous part or the current element
            assert(forall|j: int| 0 <= j < subseq.len() ==> {
                if j < idx {
                    subseq.spec_index(j) == numbers.spec_index(j) && numbers.spec_index(j) <= current_max
                } else {
                    j == idx && subseq.spec_index(j) == current_num && current_num <= current_max
                }
            });
        };
        
        // Now we can conclude isMax holds
        assert(subseq.len() > 0);
        assert(isMax(current_max, subseq));
        
        result = result.push(current_max);
        
        assert(result.len() == idx + 1);
        assert(result.spec_index(idx as int) == current_max);
        assert(isMax(result.spec_index(idx as int), numbers.subrange(0, (idx+1) as int)));
        
        idx = idx + 1;
    }
    
    result
}

}