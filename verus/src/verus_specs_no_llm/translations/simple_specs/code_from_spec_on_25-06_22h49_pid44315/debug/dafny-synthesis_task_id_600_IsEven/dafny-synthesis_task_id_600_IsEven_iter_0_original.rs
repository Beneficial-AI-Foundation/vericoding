// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsEven(n: int) -> (result: bool)
    ensures
        result <==> n % 2 == 0
{
    return false;
}

}