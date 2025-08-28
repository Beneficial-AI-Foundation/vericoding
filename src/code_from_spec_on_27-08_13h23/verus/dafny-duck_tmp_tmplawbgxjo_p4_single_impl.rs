use vstd::prelude::*;

verus! {

//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result@.len() == i,
            forall |k: usize| k < i ==> result@[k] == x@[k],
    {
        result.push(x[i]);
        i = i + 1;
    }
    
    i = 0;
    while i < y.len()
        invariant
            i <= y.len(),
            result@.len() == x.len() + i,
            forall |k: usize| k < x.len() ==> result@[k] == x@[k],
            forall |k: usize| k < i ==> result@[x.len() + k] == y@[k],
    {
        result.push(y[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}