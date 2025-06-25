// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn find(a: Vec<int>, key: int) -> (index: int)
    requires a.len() > 0;
    ensures 0 <= index <= a.len();,
            index < a.len() ==> a[index] == key;
{
}

}