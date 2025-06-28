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
            forall|k: int| 0 <= k < i ==> result[k] == x[k]
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
            forall|k: int| 0 <= k < x.len() ==> result[k] == x[k],
            forall|k: int| 0 <= k < j ==> result[x.len() as int + k] == y[k]
    {
        result.push(y[j]);
        j += 1;
    }
    
    // The postcondition should be automatically satisfied
    assert(result@ == x@ + y@);
    
    result
}

}