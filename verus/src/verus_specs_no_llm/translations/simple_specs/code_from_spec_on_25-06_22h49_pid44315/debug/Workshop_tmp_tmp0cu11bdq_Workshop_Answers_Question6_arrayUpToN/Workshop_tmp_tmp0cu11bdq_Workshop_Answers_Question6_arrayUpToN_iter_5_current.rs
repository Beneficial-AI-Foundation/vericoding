use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn arrayUpToN(n: usize) -> (a: Vec<usize>)
    ensures
        a.len() == n,
        forall|j: int| 0 <= j < n ==> a.spec_index(j) >= 0,
        forall|j: int, k: int| 0 <= j <= k < n ==> a.spec_index(j) <= a.spec_index(k)
{
    let mut a = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            forall|j: int| 0 <= j < i ==> a.spec_index(j) == j,
            forall|j: int| 0 <= j < i ==> a.spec_index(j) >= 0,
            forall|j: int, k: int| 0 <= j <= k < i ==> a.spec_index(j) <= a.spec_index(k)
    {
        a.push(i);
        i = i + 1;
    }
    
    a
}

}