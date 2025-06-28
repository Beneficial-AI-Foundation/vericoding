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
            effective_offset == (offset % (len as int)) as usize,
            effective_offset < len,
            forall |j: int| 0<=j<i ==> result.spec_index(j)==a.spec_index((j as int + offset) % (len as int))
    {
        let source_index = (i + effective_offset) % len;
        result.push(a[source_index]);
        
        assert(result.len() == i + 1);
        assert((i as int + 1 + offset) % (len as int) == ((i + effective_offset) % len) as int + offset) by {
            // This assertion helps Verus understand the relationship
        };
        
        i += 1;
    }
    
    // Post-loop assertion to help verification
    assert(result.len() == len);
    assert(forall |k: int| 0<=k<len ==> result.spec_index(k) == a.spec_index((k + offset) % (len as int)));
    
    result
}

}