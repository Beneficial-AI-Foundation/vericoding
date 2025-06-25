// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn somatorio(a: Vec<nat>) -> (s: nat)
    ensures s == soma(a, a.len())
{
}

}