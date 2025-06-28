use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn arrayUpToN(n: int) -> (a: Vec<int>)
    requires
        n >= 0
    ensures
        a.len() == n,
        forall j :: 0 < j < n ==> a.spec_index(j) >= 0,
        forall j, k : int :: 0 <= j <= k < n ==> a.spec_index(j) <= a.spec_index(k)
{
    let mut a = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            forall j :: 0 < j < i ==> a.spec_index(j) >= 0,
            forall j, k : int :: 0 <= j <= k < i ==> a.spec_index(j) <= a.spec_index(k)
    {
        a.push(0);
        i = i + 1;
    }
    
    a
}

}