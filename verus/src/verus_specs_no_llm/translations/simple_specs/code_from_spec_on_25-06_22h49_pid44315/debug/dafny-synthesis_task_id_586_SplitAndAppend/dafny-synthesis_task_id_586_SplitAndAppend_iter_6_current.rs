use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitAndAppend(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0 && n < l.len()
    ensures
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index((i + n) % l.len())
{
    let n_usize = n as usize;
    let len = l.len();
    
    // Split the sequence at position n and append the first part to the second part
    let first_part = l.subrange(0, n_usize);
    let second_part = l.subrange(n_usize, len);
    
    let result = second_part + first_part;
    
    // Length proof
    assert(second_part.len() == len - n_usize);
    assert(first_part.len() == n_usize);
    assert(result.len() == second_part.len() + first_part.len());
    
    // Prove the indexing property
    assert forall|i: int| 0 <= i < l.len() implies result.spec_index(i) == l.spec_index((i + n) % l.len()) by {
        let len_int = l.len() as int;
        let n_int = n;
        let second_len = (len - n_usize) as int;
        
        if i < second_len {
            // i is in the second part
            assert(result.spec_index(i) == second_part.spec_index(i));
            assert(second_part.spec_index(i) == l.spec_index(n_int + i));
            
            // Prove modular arithmetic: (i + n) % len == i + n when i + n < len
            assert(i + n_int < len_int);
            assert((i + n_int) % len_int == i + n_int);
            
            assert(result.spec_index(i) == l.spec_index((i + n_int) % len_int));
        } else {
            // i is in the first part
            let first_index = i - second_len;
            assert(first_index >= 0);
            assert(first_index < n_int);
            
            assert(result.spec_index(i) == first_part.spec_index(first_index));
            assert(first_part.spec_index(first_index) == l.spec_index(first_index));
            
            // Prove modular arithmetic: (i + n) % len == first_index
            assert(i + n_int == len_int + first_index);
            
            // Use the built-in modular arithmetic properties
            assert(first_index < len_int);
            assert((len_int + first_index) % len_int == first_index) by {
                // This follows from basic modular arithmetic
                assert(len_int > 0);
            };
            
            assert(result.spec_index(i) == l.spec_index((i + n_int) % len_int));
        }
    };
    
    result
}

}