use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn rotate(a: Vec<int>, offset: int) -> (b: Vec<int>)
    requires
        0<=offset
    ensures
        b.len()==a.len(),
        forall |i: int| 0<=i<a.len() ==> b.spec_index(i)==a.spec_index((i+offset)%a.len())
{
    if a.len() == 0 {
        return a;
    }
    
    let mut result = Vec::new();
    let len = a.len();
    let effective_offset = (offset % (len as int)) as usize;
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            len > 0,
            len == a.len(),
            effective_offset == (offset % (len as int)) as usize,
            effective_offset < len,
            forall |j: int| 0<=j<i ==> 
                result.spec_index(j) == a.spec_index(((j as int + effective_offset as int) % (len as int)))
    {
        let source_index = (i + effective_offset) % len;
        result.push(a[source_index]);
        
        // Help Verus understand the modular arithmetic
        assert((i as int + effective_offset as int) % (len as int) == source_index as int);
        
        i += 1;
    }
    
    // Prove the postcondition
    assert(result.len() == len);
    assert(len == a.len());
    
    // Key insight: we need to prove that effective_offset preserves the rotation property
    assert(forall |k: int| 0<=k<len ==> {
        let result_val = result.spec_index(k);
        let expected_index = (k + offset) % (len as int);
        let actual_index = (k + effective_offset as int) % (len as int);
        result_val == a.spec_index(actual_index) && actual_index == expected_index
    }) by {
        assert(forall |k: int| 0<=k<len ==> {
            (k + effective_offset as int) % (len as int) == (k + offset) % (len as int)
        }) by {
            assert(effective_offset as int == offset % (len as int));
            assert(forall |k: int| 0<=k<len ==> {
                (k + offset % (len as int)) % (len as int) == (k + offset) % (len as int)
            }) by {
                // Modular arithmetic property: (a + b % m) % m = (a + b) % m
            };
        };
    };
    
    result
}

}