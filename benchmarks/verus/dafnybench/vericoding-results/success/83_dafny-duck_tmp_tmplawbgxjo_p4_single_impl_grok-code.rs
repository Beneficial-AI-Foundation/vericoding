use vstd::prelude::*;

verus! {

//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
// </vc-spec>
// <vc-code>
{
    let mut b = Vec::new();
    proof {
        assert(b@.len() == 0);
    }
    
    for i in 0..x.len() 
        invariant
            b@.len() == i,
            b@ == x@.subrange(0, i as int)
    {
        let val = x[i];
        b.push(val);
        proof {
            assert(b@ == b@.subrange(0, (i as int)) + seq![val]);
            assert(b@[i as int] == val);
            assert(x@.subrange(0, (i + 1) as int) == x@.subrange(0, i as int) + seq![val]);
        }
    }
    proof {
        assert(b@ == x@);
    }
    
    for i in 0..y.len() 
        invariant
            b@.len() == x@.len() + i,
            b@ == x@ + y@.subrange(0, i as int)
    {
        let val = y[i];
        b.push(val);
        proof {
            assert(b@ == b@.subrange(0, x@.len() + i as int) + seq![val]);
        }
    }
    proof {
        assert(b@.len() == x@.len() + y@.len());
        assert(b@ == x@ + y@);
    }
    
    b
}
// </vc-code>

fn main() {
}

}