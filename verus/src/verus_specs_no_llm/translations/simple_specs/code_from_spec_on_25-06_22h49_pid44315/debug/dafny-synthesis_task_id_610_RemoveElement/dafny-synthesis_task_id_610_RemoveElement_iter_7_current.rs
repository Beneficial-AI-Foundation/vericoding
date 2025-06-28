use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveElement(s: Vec<int>, k: int) -> (v: Vec<int>)
    requires
        0 <= k < s.len()
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v.spec_index(i) == s.spec_index(i),
        forall|i: int| k <= i < v.len() ==> v.spec_index(i) == s.spec_index(i + 1)
{
    let mut result = Vec::new();
    let mut i = 0;
    
    // Copy elements before index k
    while i < k
        invariant
            0 <= i <= k,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == s.spec_index(j)
    {
        result.push(s[i]);
        i = i + 1;
    }
    
    // Skip element at index k and copy remaining elements
    i = k + 1;
    while i < s.len()
        invariant
            k + 1 <= i <= s.len(),
            result.len() == k + (i - k - 1),
            forall|j: int| 0 <= j < k ==> result.spec_index(j) == s.spec_index(j),
            forall|j: int| k <= j < result.len() ==> result.spec_index(j) == s.spec_index((j - k) + k + 1)
    {
        result.push(s[i]);
        i = i + 1;
    }
    
    // Prove final length
    assert(result.len() == k + (s.len() - k - 1));
    assert(k + (s.len() - k - 1) == s.len() - 1);
    
    // Prove the postconditions hold
    assert(forall|j: int| 0 <= j < k ==> result.spec_index(j) == s.spec_index(j));
    
    // For the second postcondition, we need to show that for k <= j < result.len(),
    // result.spec_index(j) == s.spec_index(j + 1)
    assert(forall|j: int| k <= j < result.len() ==> {
        let offset = j - k;
        &&& 0 <= offset < result.len() - k
        &&& result.spec_index(j) == s.spec_index(k + 1 + offset)
        &&& k + 1 + offset == j + 1
    });
    
    result
}

}