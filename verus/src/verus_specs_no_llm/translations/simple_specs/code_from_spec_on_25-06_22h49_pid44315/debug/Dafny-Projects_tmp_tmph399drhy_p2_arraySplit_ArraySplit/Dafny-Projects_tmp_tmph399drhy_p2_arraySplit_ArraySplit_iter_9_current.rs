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
            b@ == a@.subrange(0, i as int)
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
            c@ == a@.subrange(mid as int, j as int)
    {
        c.push(a[j]);
        j += 1;
    }
    
    // After loops, we have:
    // b@ == a@.subrange(0, mid as int)
    // c@ == a@.subrange(mid as int, a.len() as int)
    
    // Prove sequence equality using subrange properties
    assert(a@ == a@.subrange(0, mid as int) + a@.subrange(mid as int, a.len() as int));
    assert(b@ + c@ == a@.subrange(0, mid as int) + a@.subrange(mid as int, a.len() as int));
    assert(a@ == b@ + c@);
    
    // Length properties follow automatically
    assert(b.len() + c.len() == mid + (a.len() - mid) == a.len());
    
    // Prove size constraints for non-trivial arrays
    if a.len() > 1 {
        // When a.len() > 1, we have a.len() >= 2
        // So mid = a.len() / 2, and we need mid >= 1 and mid < a.len()
        assert(a.len() >= 2);
        assert(mid >= 1); // because a.len() >= 2 implies a.len() / 2 >= 1
        assert(mid < a.len()) by {
            // For any n >= 2, n/2 < n
            // This is true for integer division
            assert(mid * 2 <= a.len()); // property of integer division
            assert(mid < a.len()); // since mid >= 1, if mid == a.len(), then mid * 2 >= 2 * a.len() > a.len()
        };
        
        assert(a.len() > b.len()) by {
            assert(b.len() == mid);
            assert(mid < a.len());
        };
        
        assert(a.len() > c.len()) by {
            assert(c.len() == a.len() - mid);
            assert(mid >= 1);
            assert(a.len() - mid < a.len());
        };
    }
    
    (b, c)
}

}