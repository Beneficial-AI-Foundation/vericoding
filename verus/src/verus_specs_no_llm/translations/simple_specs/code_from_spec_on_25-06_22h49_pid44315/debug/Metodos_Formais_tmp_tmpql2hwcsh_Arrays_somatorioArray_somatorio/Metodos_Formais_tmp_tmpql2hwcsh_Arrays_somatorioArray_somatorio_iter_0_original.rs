// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == soma(a, a.len())
{
    return 0;
}

}