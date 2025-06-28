use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSorted(a: Vec<int>) -> (sorted: bool)
    requires
        a.len() > 0
    ensures
        sorted <== forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        !sorted ==> exists i, j :: 0 <= i < j < a.len() && a.spec_index(i) > a.spec_index(j)
{
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall k, l :: 0 <= k < l < i + 1 ==> a.spec_index(k) <= a.spec_index(l)
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}