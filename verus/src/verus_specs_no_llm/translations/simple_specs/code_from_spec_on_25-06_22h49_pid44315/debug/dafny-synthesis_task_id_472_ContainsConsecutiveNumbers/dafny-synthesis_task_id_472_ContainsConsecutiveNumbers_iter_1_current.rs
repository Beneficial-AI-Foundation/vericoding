// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsConsecutiveNumbers(a: Vec<int>) -> (result: bool)
    requires
        a.len() > 0
    ensures
        result <==> (exists|i: int| 0 <= i < a.len() - 1 && a.spec_index(i) + 1 == a.spec_index(i + 1))
{
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> a.spec_index(j) + 1 != a.spec_index(j + 1)
    {
        if a[i] + 1 == a[i + 1] {
            return true;
        }
        i = i + 1;
    }
    return false;
}

}