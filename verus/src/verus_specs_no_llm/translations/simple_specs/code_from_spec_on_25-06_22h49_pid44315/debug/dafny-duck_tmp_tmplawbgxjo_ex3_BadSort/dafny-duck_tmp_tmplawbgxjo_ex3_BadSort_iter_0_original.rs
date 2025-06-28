// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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