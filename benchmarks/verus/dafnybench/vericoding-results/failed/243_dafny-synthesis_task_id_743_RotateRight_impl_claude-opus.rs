use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
// </vc-spec>
// <vc-code>
{
    if l.len() == 0 {
        return l;
    }
    
    let len = l.len();
    
    let mut r_vec: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            r_vec.len() == i,
            r_vec@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] r_vec@[j] == l[(j - n + (len as int)) % (len as int)],
    {
        // Calculate the source index for rotation
        let ghost n_mod = n % (len as int);
        let ghost src_idx = (i as int - n_mod + (len as int)) % (len as int);
        
        // We need to compute this in executable code using usize arithmetic
        let n_mod_usize = if n >= 0 && n < len as int {
            n as usize
        } else {
            ((n % (len as int)) + (len as int)) as usize % len
        };
        
        let idx = if i >= n_mod_usize {
            i - n_mod_usize
        } else {
            len - (n_mod_usize - i)
        };
        
        proof {
            // Prove that idx matches our spec calculation
            if n_mod >= 0 {
                if i as int >= n_mod {
                    assert(idx as int == i as int - n_mod);
                    assert(idx as int == (i as int - n_mod + (len as int)) % (len as int));
                } else {
                    assert(idx as int == len as int - (n_mod - i as int));
                    assert(idx as int == (i as int - n_mod + (len as int)));
                    assert(idx as int == (i as int - n_mod + (len as int)) % (len as int));
                }
            } else {
                let n_mod_pos = ((n % (len as int)) + (len as int)) % (len as int);
                assert(n_mod_pos >= 0);
                assert((i as int - n + (len as int)) % (len as int) == (i as int - n_mod_pos + (len as int)) % (len as int));
            }
            assert(0 <= idx < len);
            assert(idx as int == src_idx);
        }
        
        r_vec.push(l[idx as int]);
        i = i + 1;
    }
    
    let r = r_vec@;
    
    proof {
        assert(r.len() == l.len());
        assert forall|i: int| 0 <= i < l.len() implies r[i] == l[(i - n + (len as int)) % (len as int)] by {
            assert(r[i] == r_vec@[i]);
        }
    }
    
    r
}
// </vc-code>

fn main() {}

}