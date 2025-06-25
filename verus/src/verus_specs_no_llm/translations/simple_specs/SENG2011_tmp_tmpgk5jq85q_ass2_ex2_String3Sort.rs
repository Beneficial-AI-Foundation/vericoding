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

fn String3Sort(a: String) -> (b: String)
    requires
        a.len() == 3
    ensures
        Sorted(b, 0, b.len()),
        a.len() == b.len(),
        multiset
{
    return String::new();
}

}