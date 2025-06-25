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

fn Somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == SomaAte(a,a.len())
{
    return 0;
}

}