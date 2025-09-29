use vstd::prelude::*;

verus! {

//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>

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
    let mut result = Vec::new();
    
    for i in 0..x.len()
        invariant
            result@.len() == i,
            result@ == x@.subrange(0, i as int),
    {
        result.push(x[i]);
    }
    
    for i in 0..y.len()
        invariant
            result@.len() == x@.len() + i,
            result@ == x@ + y@.subrange(0, i as int),
    {
        result.push(y[i]);
    }
    
    result
}
// </vc-code>

fn main() {
}

}