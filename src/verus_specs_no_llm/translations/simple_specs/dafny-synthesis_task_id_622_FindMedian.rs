// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMedian(a: Vec<int>, b: Vec<int>) -> (median: int)
    requires
        a != null && b != null,
        a.len() == b.len(),
        a.len() > 0,
        forall i :: 0 <= i < a.len() - 1 ==> a.spec_index(i) <= a.spec_index(i + 1),
        forall i :: 0 <= i < b.len() - 1 ==> b.spec_index(i) <= b.spec_index(i + 1)
    ensures
        median == if (a.len() % 2 == 0) then (a.spec_index(a.len() / 2 - 1) + b.spec_index(0)) / 2 else a.spec_index(a.len() / 2)
{
    return 0;
}

}