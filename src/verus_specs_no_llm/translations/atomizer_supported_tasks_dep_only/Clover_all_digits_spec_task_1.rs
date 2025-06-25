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

fn allDigits(s: String) -> (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < s.len() ==> s.spec_index(i) in "0123456789")
{
    return false;
}

}