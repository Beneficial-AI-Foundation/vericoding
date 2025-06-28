use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn single(x: Vec<int>, y: Vec<int>) -> (b: Vec<int>)
    requires
        x.len() > 0,
        y.len() > 0
    ensures
        b@ == x@ + y@
{
    let mut result = Vec::new();
    
    // Add all elements from x
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            result@ == x@.subrange(0, i as int)
    {
        result.push(x[i]);
        i += 1;
    }
    
    // Add all elements from y
    let mut j: usize = 0;
    while j < y.len()
        invariant
            j <= y.len(),
            result.len() == x.len() + j,
            result@ == x@ + y@.subrange(0, j as int)
    {
        result.push(y[j]);
        j += 1;
    }
    
    result
}

}