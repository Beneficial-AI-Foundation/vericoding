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
    let mut result = Seq::empty();
    let mut current_max = numbers.index(0);
    result = result.push(current_max);
    
    assert(result.len() == 1);
    assert(isMax(result.spec_index(0), numbers.subrange(0, 1)));
    
    let mut idx: usize = 1;
    while idx < numbers.len()
        invariant
            1 <= idx <= numbers.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < result.len() ==> isMax(result.spec_index(i), numbers.subrange(0, i+1)),
            current_max == result.spec_index((idx-1) as int)
    {
        let old_max = current_max;
        if numbers.index(idx) > current_max {
            current_max = numbers.index(idx);
        }
        
        // Prove that current_max is the maximum in the range [0, idx+1)
        assert(current_max >= old_max);
        assert(current_max >= numbers.index(idx as int));
        assert(forall|j: int| 0 <= j < idx ==> numbers.spec_index(j) <= old_max);
        assert(forall|j: int| 0 <= j <= idx ==> numbers.spec_index(j) <= current_max);
        assert(exists|k: int| 0 <= k <= idx && numbers.spec_index(k) == current_max);
        
        result = result.push(current_max);
        
        assert(result.len() == idx + 1);
        assert(isMax(current_max, numbers.subrange(0, (idx+1) as int)));
        
        idx = idx + 1;
    }
    
    result
}

}