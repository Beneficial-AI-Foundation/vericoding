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
    
    // Prove sequence equality using subrange axiom
    assert(a@ == a@.subrange(0, a.len() as int));
    assert(a@.subrange(0, a.len() as int) == a@.subrange(0, mid as int) + a@.subrange(mid as int, a.len() as int));
    assert(b@ + c@ == a@.subrange(0, mid as int) + a@.subrange(mid as int, a.len() as int));
    
    // Length properties
    assert(b.len() + c.len() == mid + (a.len() - mid) == a.len());
    
    // Prove size constraints for non-trivial arrays
    if a.len() > 1 {
        assert(a.len() >= 2);
        assert(mid >= 1) by {
            assert(a.len() / 2 >= 2 / 2);
        };
        assert(mid < a.len()) by {
            // For integer division: if n >= 2, then n/2 < n
            if a.len() == 2 {
                assert(mid == 1);
            } else {
                // a.len() >= 3, so mid <= (a.len() - 1) / 2 + 1/2 < a.len()
                assert(mid * 2 <= a.len());
                assert(mid < a.len());
            }
        };
        
        assert(a.len() > b.len());
        assert(a.len() > c.len()) by {
            assert(c.len() == a.len() - mid);
            assert(a.len() - mid < a.len());
        };
    }
    
    (b, c)
}

}