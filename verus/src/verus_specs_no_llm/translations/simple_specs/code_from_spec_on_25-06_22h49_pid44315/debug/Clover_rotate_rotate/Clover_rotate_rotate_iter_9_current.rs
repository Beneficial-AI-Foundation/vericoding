use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma for modular arithmetic
proof fn lemma_mod_add_property(a: int, b: int, m: int)
    requires m > 0
    ensures (a + b) % m == (a % m + b % m) % m
{
    // This is a fundamental property of modular arithmetic
    // Verus can prove this automatically with the right hints
    assert((a + b) % m == (a % m + b % m) % m) by(nonlinear_arith);
}

proof fn lemma_effective_offset_property(i: int, offset: int, len: int, effective_offset: int)
    requires 
        len > 0,
        effective_offset == offset % len,
        0 <= i < len,
        0 <= effective_offset < len
    ensures (i + effective_offset) % len == (i + offset) % len
{
    // Since effective_offset = offset % len, we have offset = k * len + effective_offset for some k
    // So i + offset = i + k * len + effective_offset
    // Therefore (i + offset) % len = (i + effective_offset) % len
    lemma_mod_add_property(i, offset, len);
    assert(offset % len == effective_offset);
    assert((i + offset) % len == (i + offset % len) % len) by(nonlinear_arith);
    assert((i + offset % len) % len == (i + effective_offset) % len);
}

fn rotate(a: Vec<int>, offset: int) -> (b: Vec<int>)
    requires
        0 <= offset
    ensures
        b.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> b.spec_index(i) == a.spec_index((i + offset) % a.len())
{
    if a.len() == 0 {
        return a;
    }
    
    let mut result = Vec::new();
    let len = a.len();
    let effective_offset = (offset % (len as int)) as usize;
    
    // Establish key properties about effective_offset
    assert(0 <= effective_offset < len) by {
        assert(len > 0);
        assert(len as int > 0);
        assert(0 <= offset % (len as int) < len as int) by(nonlinear_arith);
        assert(0 <= effective_offset < len);
    };
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            len > 0,
            len == a.len(),
            effective_offset == (offset % (len as int)) as usize,
            0 <= effective_offset < len,
            forall |j: int| 0 <= j < i ==> 
                result.spec_index(j) == a.spec_index((j + offset) % (len as int))
    {
        let source_index = (i + effective_offset) % len;
        
        // Prove the modular arithmetic relationship before pushing
        proof {
            assert(0 <= i as int < len as int);
            assert(0 <= effective_offset as int < len as int);
            lemma_effective_offset_property(i as int, offset, len as int, effective_offset as int);
            assert((i as int + effective_offset as int) % (len as int) == (i as int + offset) % (len as int));
            assert(source_index == (i + effective_offset) % len);
            assert(source_index as int == (i as int + effective_offset as int) % (len as int));
            assert(source_index as int == (i as int + offset) % (len as int));
        }
        
        result.push(a[source_index]);
        i += 1;
    }
    
    // Final assertions to help verification
    assert(result.len() == a.len());
    assert(forall |j: int| 0 <= j < a.len() ==> 
        result.spec_index(j) == a.spec_index((j + offset) % (a.len() as int)));
    
    result
}

}