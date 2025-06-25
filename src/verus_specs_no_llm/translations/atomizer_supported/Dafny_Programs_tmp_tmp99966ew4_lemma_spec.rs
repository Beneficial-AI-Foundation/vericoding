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

fn FindZero(a: Vec<int>) -> (index: int)
    requires
        a != null,
        forall i :: 0 <= i < a.len() ==> 0 <= a.spec_index(i),
        forall i :: 0 < i < a.len() ==> a.spec_index(i-1)-1 <= a.spec_index(i)
    ensures
        index < 0  ==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) != 0,
        0 <= index ==> index < a.len() && a.spec_index(index) == 0
{
    return 0;
}

}