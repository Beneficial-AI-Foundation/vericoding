use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a == old(a),
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b.spec_index(i) == a.spec_index(a.len() - i - 1)
{
    let mut b = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            b.len() == i,
            forall|k: int| 0 <= k < i ==> b.spec_index(k) == a.spec_index(a.len() - k - 1),
            a.len() > 0
    {
        // Calculate the index we're taking from 'a'
        let src_index = a.len() - 1 - i;
        
        // Add proof assertions to help with bounds checking
        assert(i < a.len());
        assert(a.len() >= 1);
        assert(src_index < a.len());
        assert(src_index == a.len() - 1 - i);
        
        // Help prove the invariant will be maintained
        proof {
            assert forall|k: int| 0 <= k < i ==> b.spec_index(k) == a.spec_index(a.len() - k - 1) by {};
            assert(b.len() == i);
            assert(src_index == a.len() - (i as int) - 1);
            assert(src_index == a.len() - ((i + 1) as int));
        }
        
        b.push(a[src_index]);
        i = i + 1;
        
        // Help prove the invariant after the iteration
        proof {
            let old_i = (i - 1) as int;
            assert(b.len() == i);
            assert(b.spec_index(old_i) == a.spec_index(a.len() - old_i - 1));
        }
    }
    
    b
}

}