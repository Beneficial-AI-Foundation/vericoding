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
    lemma_mod_add_property(i, offset, len);
    lemma_mod_add_property(i, effective_offset, len);
    assert(offset % len == effective_offset);
    assert((i + offset) % len == (i % len + offset % len) % len) by(nonlinear_arith);
    assert((i + effective_offset) % len == (i % len + effective_offset % len) % len) by(nonlinear_arith);
    assert(i % len == i) by(nonlinear_arith);
    assert(effective_offset % len == effective_offset) by(nonlinear_arith);
    assert((i + offset) % len == (i + effective_offset) % len) by(nonlinear_arith);
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
        
        // Prove that source_index gives us the right element
        assert(0 <= source_index < len);
        assert(source_index as int == (i as int + effective_offset as int) % (len as int));
        
        proof {
            lemma_effective_offset_property(i as int, offset, len as int, effective_offset as int);
            assert((i as int + effective_offset as int) % (len as int) == (i as int + offset) % (len as int));
        }
        
        result.push(a[source_index]);
        
        // Help verify the loop invariant
        assert(forall |j: int| 0 <= j < i + 1 ==> 
            result.spec_index(j) == a.spec_index((j + offset) % (len as int))) by {
            assert(forall |j: int| 0 <= j < i ==> 
                result.spec_index(j) == a.spec_index((j + offset) % (len as int)));
            assert(result.spec_index(i as int) == a.spec_index((i as int + offset) % (len as int)));
        };
        
        i += 1;
    }
    
    result
}

}