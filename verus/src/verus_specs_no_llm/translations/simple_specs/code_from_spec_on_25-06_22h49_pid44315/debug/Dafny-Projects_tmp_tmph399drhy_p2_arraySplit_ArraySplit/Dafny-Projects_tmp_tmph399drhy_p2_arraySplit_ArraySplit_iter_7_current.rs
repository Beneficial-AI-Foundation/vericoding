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
    
    // Prove sequence equality using extensional equality
    assert(a@ =~= b@ + c@) by {
        assert((b@ + c@).len() == a@.len()) by {
            assert(b@.len() == mid as int);
            assert(c@.len() == (a.len() - mid) as int);
            assert(b@.len() + c@.len() == a@.len());
        };
        
        assert(forall|idx: int| 0 <= idx < a@.len() ==> (b@ + c@)[idx] == a@[idx]) by {
            assert(forall|idx: int| 0 <= idx < mid as int ==> (b@ + c@)[idx] == a@[idx]) by {
                assert(forall|idx: int| 0 <= idx < mid as int ==> (b@ + c@)[idx] == b@[idx]);
                assert(forall|idx: int| 0 <= idx < mid as int ==> b@[idx] == a@[idx]);
            };
            
            assert(forall|idx: int| mid as int <= idx < a@.len() ==> (b@ + c@)[idx] == a@[idx]) by {
                assert(forall|idx: int| mid as int <= idx < a@.len() ==> {
                    let c_idx = idx - mid as int;
                    &&& 0 <= c_idx < c@.len()
                    &&& (b@ + c@)[idx] == c@[c_idx]
                    &&& c@[c_idx] == a@[idx]
                });
            };
        };
    };
    
    // The sequence equality should now be established
    assert(a@ == b@ + c@);
    
    // Prove size constraints for non-trivial arrays
    if a.len() > 1 {
        // Key insight: when a.len() > 1, we have a.len() >= 2
        // So mid = a.len() / 2 satisfies: 1 <= mid < a.len()
        assert(mid >= 1) by {
            assert(a.len() >= 2);
            // For any n >= 2, n/2 >= 1 in integer division
        };
        
        assert(mid < a.len()) by {
            assert(a.len() >= 2);
            // For any n >= 2, n/2 < n in integer division
            // This is because n/2 <= (n-1)/2 + 1/2 < n when n >= 2
        };
        
        assert(b.len() == mid);
        assert(a.len() > b.len()) by {
            assert(b.len() == mid);
            assert(mid < a.len());
        };
        
        assert(c.len() == a.len() - mid);
        assert(a.len() > c.len()) by {
            assert(c.len() == a.len() - mid);
            assert(mid >= 1);
            assert(a.len() - mid < a.len());
        };
    }
    
    (b, c)
}

}