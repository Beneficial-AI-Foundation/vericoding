// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn buscar(a: Vec<int>, x: int) -> (r: int)
    ensures
        r < 0 ==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) != x,
        0 <= r < a.len() ==> a.spec_index(r) == x
{
    return 0;
}

}