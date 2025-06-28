// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires
        0 <= l < r <= a.len()
    ensures
        ret.spec_index(..) == a.spec_index(l..r)
{
    let mut result = Vec::new();
    let mut i = l;
    
    while i < r
        invariant
            l <= i <= r,
            result.len() == i - l,
            result.spec_index(..) == a.spec_index(l..i)
    {
        result.push(a[i]);
        i = i + 1;
    }
    
    result
}

}