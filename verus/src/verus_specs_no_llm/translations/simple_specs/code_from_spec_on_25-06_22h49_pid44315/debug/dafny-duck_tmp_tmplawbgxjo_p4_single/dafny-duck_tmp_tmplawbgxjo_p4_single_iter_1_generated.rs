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
        b.spec_index(..) == x.spec_index(..) + y.spec_index(..)
{
    let mut result = Vec::new();
    
    // Add all elements from x
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.spec_index(..) == x.spec_index(..i as int)
    {
        result.push(x[i]);
        i += 1;
    }
    
    // Add all elements from y
    let mut j = 0;
    while j < y.len()
        invariant
            j <= y.len(),
            result.spec_index(..) == x.spec_index(..) + y.spec_index(..j as int)
    {
        result.push(y[j]);
        j += 1;
    }
    
    result
}

}