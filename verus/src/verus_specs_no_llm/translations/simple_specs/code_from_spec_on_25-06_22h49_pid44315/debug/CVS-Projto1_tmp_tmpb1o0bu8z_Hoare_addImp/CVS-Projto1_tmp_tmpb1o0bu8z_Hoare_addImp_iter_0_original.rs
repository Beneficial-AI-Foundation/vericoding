// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn addImp(l: List<int>) -> (s: int)
    ensures
        s == add(l)
{
    return 0;
}

}