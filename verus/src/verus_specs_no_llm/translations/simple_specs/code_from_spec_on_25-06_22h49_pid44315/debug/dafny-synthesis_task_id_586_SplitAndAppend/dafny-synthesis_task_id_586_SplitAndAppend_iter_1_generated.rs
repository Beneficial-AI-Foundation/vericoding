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
    
    // Proof that the result satisfies the postcondition
    assert(result.len() == l.len());
    
    // Prove the indexing property
    assert forall|i: int| 0 <= i < l.len() implies result.spec_index(i) == l.spec_index((i + n) % l.len()) by {
        let len_int = l.len() as int;
        if i < len_int - n {
            // i is in the second part (indices n to len-1 from original)
            assert(result.spec_index(i) == second_part.spec_index(i));
            assert(second_part.spec_index(i) == l.spec_index(i + n));
            assert((i + n) % len_int == i + n); // since i + n < len
        } else {
            // i is in the first part (indices 0 to n-1 from original)
            let offset = i - (len_int - n);
            assert(result.spec_index(i) == first_part.spec_index(offset));
            assert(first_part.spec_index(offset) == l.spec_index(offset));
            assert((i + n) % len_int == offset); // since i + n >= len
        }
    }
    
    result
}

}