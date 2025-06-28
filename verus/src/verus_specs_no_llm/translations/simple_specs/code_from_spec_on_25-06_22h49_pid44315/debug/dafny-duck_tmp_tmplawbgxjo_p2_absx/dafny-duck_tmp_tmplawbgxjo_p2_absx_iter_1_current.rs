use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn absx(x: Vec<int>) -> (y: Vec<int>)
    ensures
        y.len() == x.len(),
        forall i :: 0 <= i < y.len() ==> y.spec_index(i) == abs(x.spec_index(i))
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall j :: 0 <= j < i ==> result.spec_index(j) == abs(x.spec_index(j))
    {
        result.push(abs(x[i]));
        i += 1;
    }
    
    return result;
}

}