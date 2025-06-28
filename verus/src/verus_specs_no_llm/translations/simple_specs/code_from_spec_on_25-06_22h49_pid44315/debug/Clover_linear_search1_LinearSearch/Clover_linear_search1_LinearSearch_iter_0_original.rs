// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    ensures
        0<=n<=a.len(),
        n==a.len() || a.spec_index(n)==e,
        forall i::0<=i < n ==> e!=a.spec_index(i)
{
    return 0;
}

}