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
        let len_int = l.len();
        let n_int = n;
        let second_len = len_int - n_int;
        
        // Key insight: we need to establish that len_int > 0 for modular arithmetic
        assert(len_int > 0) by {
            assert(n >= 0 && n < l.len());
        };
        
        if i < second_len {
            // i is in the second part
            assert(result.spec_index(i) == second_part.spec_index(i));
            assert(second_part.spec_index(i) == l.spec_index((n_usize + (i as usize)) as int));
            assert((n_usize + (i as usize)) as int == n_int + i);
            
            // Prove modular arithmetic: (i + n) % len == i + n when i + n < len
            assert(i + n_int < len_int) by {
                assert(i < second_len);
                assert(second_len == len_int - n_int);
            };
            
            // Use built-in property that for 0 <= a < b, a % b == a
            assert((i + n_int) % len_int == i + n_int);
            
            assert(result.spec_index(i) == l.spec_index((i + n_int) % len_int));
        } else {
            // i is in the first part
            let first_index = i - second_len;
            assert(first_index >= 0);
            assert(first_index < n_int);
            
            assert(result.spec_index(i) == first_part.spec_index(first_index));
            assert(first_part.spec_index(first_index) == l.spec_index((first_index as usize) as int));
            assert((first_index as usize) as int == first_index);
            
            // Prove modular arithmetic: (i + n) % len == first_index
            assert(i + n_int == len_int + first_index) by {
                assert(i == second_len + first_index);
                assert(second_len == len_int - n_int);
            };
            
            // Use built-in modular arithmetic: (a + b) % a == b % a when a > 0
            assert((len_int + first_index) % len_int == first_index % len_int) by {
                assert(len_int > 0);
            };
            
            // Since 0 <= first_index < len_int, first_index % len_int == first_index
            assert(first_index % len_int == first_index) by {
                assert(first_index >= 0);
                assert(first_index < len_int);
            };
            
            assert((i + n_int) % len_int == first_index);
            assert(result.spec_index(i) == l.spec_index((i + n_int) % len_int));
        }
    };
    
    result
}

}