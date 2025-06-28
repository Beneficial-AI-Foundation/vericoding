use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    ensures
        0<=n<=a.len(),
        n==a.len() || a.spec_index(n)==e,
        forall|i: int| 0<=i < n ==> e!=a.spec_index(i)
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> e != a.spec_index(j),
            i <= a.len()
    {
        if a[i] == e {
            assert(a.spec_index(i as int) == e);
            assert(forall|j: int| 0 <= j < i ==> e != a.spec_index(j));
            return i as int;
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < i ==> e != a.spec_index(j));
    return a.len() as int;
}

}