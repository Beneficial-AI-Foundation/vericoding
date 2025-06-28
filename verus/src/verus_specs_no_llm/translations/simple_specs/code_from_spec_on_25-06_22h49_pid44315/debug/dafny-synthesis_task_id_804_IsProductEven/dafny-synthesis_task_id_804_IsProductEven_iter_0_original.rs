// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

fn IsProductEven(a: Vec<int>) -> (result: bool)
    ensures
        result <==> exists i :: 0 <= i < a.len() && IsEven(a.spec_index(i))
{
    return false;
}

}