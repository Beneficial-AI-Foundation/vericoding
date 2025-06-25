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

fn Getmini(a: Vec<int>) -> (mini: nat)
    requires
        a.len() > 0
    ensures
        0 <= mini < a.len() // mini is an index of a,
        forall x :: 0 <= x < a.len() ==> a.spec_index(mini) <= a.spec_index(x) // a.spec_index(mini) is the minimum value,
        forall x :: 0 <= x < mini ==> a.spec_index(mini) < a.spec_index(x) // a.spec_index(mini) is the first min
{
    return 0;
}

}