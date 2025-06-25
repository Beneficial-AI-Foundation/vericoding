// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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