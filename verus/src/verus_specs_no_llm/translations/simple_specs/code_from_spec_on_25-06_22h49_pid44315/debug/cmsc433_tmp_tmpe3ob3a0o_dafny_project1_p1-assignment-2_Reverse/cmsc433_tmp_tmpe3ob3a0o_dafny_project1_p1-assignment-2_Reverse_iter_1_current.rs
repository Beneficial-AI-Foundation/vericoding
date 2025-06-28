use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<int>) -> (aRev: Vec<int>)
    ensures
        aRev.len() == a.len(),
        forall i : int :: 0 <= i < a.len() ==> a.spec_index(i) == aRev.spec_index(aRev.len()-i-1),
        fresh(aRev) // Indicates returned object is newly created in method body
{
    let mut aRev = Vec::new();
    let mut j: usize = 0;
    
    while j < a.len()
        invariant
            j <= a.len(),
            aRev.len() == j,
            forall k : int :: 0 <= k < j ==> a.spec_index(a.len() - 1 - k) == aRev.spec_index(k),
    {
        let index = a.len() - 1 - j;
        aRev.push(a[index]);
        j = j + 1;
    }
    
    return aRev;
}

}