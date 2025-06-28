// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsOdd(n: int) -> (result: bool)
    ensures
        result <==> n % 2 == 1
{
    return false;
}

}