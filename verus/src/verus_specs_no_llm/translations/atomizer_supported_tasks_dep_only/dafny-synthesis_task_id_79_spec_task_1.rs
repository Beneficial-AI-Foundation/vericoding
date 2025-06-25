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

fn IsLengthOdd(s: String) -> (result: bool)
    ensures
        result <==> s.len() % 2 == 1
{
    return false;
}

}