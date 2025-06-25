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

fn Find(blood: Vec<int>, key: int) -> (index: int)
    requires
        blood != null
    ensures
        0 <= index ==> index < blood.len() && blood.spec_index(index) == key,
        index < 0 ==> forall k :: 0 <= k < blood.len() ==> blood.spec_index(k) != key
{
    return 0;
}

}