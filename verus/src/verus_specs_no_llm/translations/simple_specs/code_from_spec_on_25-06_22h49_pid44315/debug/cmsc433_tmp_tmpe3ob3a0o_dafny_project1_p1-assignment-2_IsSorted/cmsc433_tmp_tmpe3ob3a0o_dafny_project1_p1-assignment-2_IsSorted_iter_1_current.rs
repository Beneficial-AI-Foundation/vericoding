use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSorted(a: Vec<int>) -> (isSorted: bool)
    ensures
        isSorted <==> forall j : int :: 1 <= j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j)
{
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall j : int :: 1 <= j < i ==> a.spec_index(j-1) <= a.spec_index(j)
    {
        if a[i-1] > a[i] {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}