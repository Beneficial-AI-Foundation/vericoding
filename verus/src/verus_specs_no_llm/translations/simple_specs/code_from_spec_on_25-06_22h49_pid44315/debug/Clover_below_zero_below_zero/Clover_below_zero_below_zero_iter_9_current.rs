use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn below_zero(operations: Seq<int>) -> (result: (Vec<int>, bool))
    requires operations.len() < usize::MAX
    ensures
        result.0.len() == operations.len() + 1,
        result.0.spec_index(0) == 0,
        forall|i: int| 0 <= i < result.0.len()-1 ==> result.0.spec_index(i+1) == result.0.spec_index(i) + operations.spec_index(i),
        result.1 == true ==> (exists|i: int| 1 <= i <= operations.len() && result.0.spec_index(i) < 0),
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() ==> result.0.spec_index(i) >= 0
{
    let mut s = Vec::new();
    s.push(0);
    
    let mut current_sum = 0;
    let mut found_negative = false;
    
    let mut idx: usize = 0;
    while idx < operations.len()
        invariant
            s.len() == idx + 1,
            s.spec_index(0) == 0,
            current_sum == s.spec_index(idx as int),
            forall|i: int| 0 <= i < idx ==> s.spec_index(i+1) == s.spec_index(i) + operations.spec_index(i),
            found_negative ==> (exists|i: int| 1 <= i <= idx && s.spec_index(i) < 0),
            !found_negative ==> forall|i: int| 0 <= i <= idx ==> s.spec_index(i) >= 0,
            0 <= idx <= operations.len(),
            idx < usize::MAX,
    {
        let operation_value = operations[idx as int];
        current_sum = current_sum + operation_value;
        s.push(current_sum);
        
        if current_sum < 0 {
            found_negative = true;
        }
        
        idx = idx + 1;
    }
    
    // Add proof assertions to help verification
    assert(s.len() == operations.len() + 1);
    assert(forall|i: int| 0 <= i < s.len()-1 ==> s.spec_index(i+1) == s.spec_index(i) + operations.spec_index(i));
    
    if found_negative {
        assert(exists|i: int| 1 <= i <= operations.len() && s.spec_index(i) < 0);
    } else {
        assert(forall|i: int| 0 <= i < s.len() ==> s.spec_index(i) >= 0);
    }
    
    (s, found_negative)
}

}