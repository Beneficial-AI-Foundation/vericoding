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

fn BadSort(a: String) -> (b: String)
    requires
        forall i :: 0<=i<a.len() ==> a.spec_index(i) in
{
    return String::new();
}

}