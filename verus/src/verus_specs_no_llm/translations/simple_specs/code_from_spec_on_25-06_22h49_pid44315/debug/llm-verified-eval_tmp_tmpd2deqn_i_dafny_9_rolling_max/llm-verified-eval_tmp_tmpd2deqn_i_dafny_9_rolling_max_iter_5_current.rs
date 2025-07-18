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
    let mut current_max = numbers[0];
    result = result.push(current_max);
    
    // Prove the base case
    assert(result.len() == 1);
    assert(numbers.subrange(0, 1).len() == 1);
    assert(numbers.subrange(0, 1)[0] == numbers[0]);
    assert(current_max == numbers[0]);
    
    // Prove isMax for base case
    assert(numbers.subrange(0, 1).len() > 0);
    assert(numbers.subrange(0, 1)[0] == current_max);
    assert(forall|j: int| 0 <= j < numbers.subrange(0, 1).len() ==> numbers.subrange(0, 1)[j] <= current_max) by {
        assert(numbers.subrange(0, 1).len() == 1);
        assert(numbers.subrange(0, 1)[0] <= current_max);
    };
    assert(exists|k: int| 0 <= k < numbers.subrange(0, 1).len() && numbers.subrange(0, 1)[k] == current_max) by {
        assert(numbers.subrange(0, 1)[0] == current_max);
    };
    assert(isMax(result[0], numbers.subrange(0, 1)));
    
    let mut idx: usize = 1;
    while idx < numbers.len()
        invariant
            1 <= idx <= numbers.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < result.len() ==> isMax(result[i], numbers.subrange(0, i+1)),
            current_max == result[(idx-1) as int]
    {
        let current_num = numbers[idx as int];
        
        if current_num > current_max {
            current_max = current_num;
        }
        
        // Prove that current_max is indeed the maximum in subrange [0, idx+1)
        let subseq = numbers.subrange(0, (idx+1) as int);
        
        // Prove current_max appears in the subsequence
        assert(exists|k: int| 0 <= k < subseq.len() && subseq[k] == current_max) by {
            if current_max == current_num {
                assert(subseq[idx as int] == current_max);
            } else {
                // current_max didn't change, so it was the max of previous elements
                assert(current_max >= current_num);
                assert(isMax(current_max, numbers.subrange(0, idx as int)));
                assert(exists|k: int| 0 <= k < idx && numbers[k] == current_max);
                assert(forall|k: int| 0 <= k < idx ==> subseq[k] == numbers[k]) by {
                    assert(numbers.subrange(0, idx as int) == subseq.subrange(0, idx as int));
                };
            }
        };
        
        // Prove current_max is >= all elements in the subsequence
        assert(forall|j: int| 0 <= j < subseq.len() ==> subseq[j] <= current_max) by {
            assert(forall|j: int| 0 <= j < idx ==> numbers[j] <= current_max) by {
                if current_max == current_num {
                    assert(forall|j: int| 0 <= j < idx ==> numbers[j] <= result[(idx-1) as int]);
                    assert(result[(idx-1) as int] <= current_num);
                } else {
                    assert(isMax(current_max, numbers.subrange(0, idx as int)));
                }
            };
            assert(current_max >= current_num);
            assert(forall|j: int| 0 <= j < subseq.len() ==> {
                if j < idx {
                    subseq[j] == numbers[j] && numbers[j] <= current_max
                } else {
                    j == idx && subseq[j] == current_num && current_num <= current_max
                }
            });
        };
        
        // Now we can conclude isMax holds
        assert(subseq.len() > 0);
        assert(isMax(current_max, subseq));
        
        result = result.push(current_max);
        
        assert(result.len() == idx + 1);
        assert(result[idx as int] == current_max);
        assert(isMax(result[idx as int], numbers.subrange(0, (idx+1) as int)));
        
        idx = idx + 1;
    }
    
    result
}

}