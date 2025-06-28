// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsDivisibleBy11(n: int) -> (result: bool)
    ensures
        result <==> n % 11 == 0
{
    return false;
}

}