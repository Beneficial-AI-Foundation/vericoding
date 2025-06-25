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

fn firste(a: Vec<char>) -> (c: int)
    ensures
        -1 <= c < a.len(),
        0 <= c < a.len() ==> a.spec_index(c) == 'e' && forall x :: 0 <= x < c ==> a.spec_index(x) != 'e',
        c == -1 ==> forall x :: 0 <= x < a.len() ==> a.spec_index(x) != 'e'
{
    return 0;
}

}