use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySplit(a: Vec<int>) -> (b: Vec<int>, c: Vec<int>)
    ensures
        a@ == b@ + c@,
        a.len() == b.len() + c.len(),
        a.len() > 1 ==> a.len() > b.len(),
        a.len() > 1 ==> a.len() > c.len()
{
    let mid = a.len() / 2;
    let mut b = Vec::new();
    let mut c = Vec::new();
    
    // Copy first half to b
    let mut i: usize = 0;
    while i < mid
        invariant
            i <= mid,
            mid <= a.len(),
            b.len() == i,
            forall|j: int| 0 <= j < i as int ==> b@[j] == a@[j]
    {
        b.push(a[i]);
        i += 1;
    }
    
    // Copy second half to c
    let mut j: usize = mid;
    while j < a.len()
        invariant
            mid <= j <= a.len(),
            c.len() == j - mid,
            forall|k: int| 0 <= k < (j - mid) as int ==> c@[k] == a@[mid as int + k]
    {
        c.push(a[j]);
        j += 1;
    }
    
    // Establish the postconditions
    assert(b.len() == mid);
    assert(c.len() == a.len() - mid);
    assert(a.len() == b.len() + c.len());
    
    // Prove that b@ + c@ == a@
    assert(b@.len() == mid as int);
    assert(c@.len() == (a.len() - mid) as int);
    assert((b@ + c@).len() == a@.len());
    
    assert forall|idx: int| 0 <= idx < a@.len() implies 
        (b@ + c@)[idx] == a@[idx]
    by {
        if idx < mid as int {
            assert(idx < b@.len());
            assert((b@ + c@)[idx] == b@[idx]);
            assert(b@[idx] == a@[idx]);
        } else {
            let c_idx = idx - mid as int;
            assert(0 <= c_idx < c@.len());
            assert(c@[c_idx] == a@[idx]);
            assert(idx >= b@.len());
            assert((b@ + c@)[idx] == c@[idx - b@.len()]);
            assert(idx - b@.len() == c_idx);
            assert((b@ + c@)[idx] == c@[c_idx]);
            assert((b@ + c@)[idx] == a@[idx]);
        }
    };
    
    // Use extensional equality to prove sequence equality
    assert(b@ + c@ == a@) by {
        assert((b@ + c@).len() == a@.len());
        assert(forall|idx: int| 0 <= idx < a@.len() ==> (b@ + c@)[idx] == a@[idx]);
    };
    
    // Prove size constraints for non-trivial arrays
    if a.len() > 1 {
        // Prove mid < a.len()
        assert(mid < a.len()) by {
            assert(a.len() >= 2);
            assert(mid == a.len() / 2);
            // For integer division, when a.len() >= 2, a.len() / 2 < a.len()
            if a.len() % 2 == 0 {
                assert(mid * 2 == a.len());
                assert(mid >= 1);
                assert(mid < a.len());
            } else {
                assert(mid * 2 + 1 == a.len());
                assert(mid >= 1);
                assert(mid < a.len());
            }
        };
        
        assert(b.len() == mid);
        assert(b.len() < a.len());
        
        // Prove mid >= 1 when a.len() > 1
        assert(mid >= 1) by {
            assert(a.len() >= 2);
            assert(mid == a.len() / 2);
            assert(2 / 2 == 1);
        };
        
        assert(c.len() == a.len() - mid);
        assert(c.len() < a.len()) by {
            assert(mid >= 1);
            assert(c.len() == a.len() - mid);
            assert(a.len() - mid < a.len());
        };
    }
    
    (b, c)
}

}