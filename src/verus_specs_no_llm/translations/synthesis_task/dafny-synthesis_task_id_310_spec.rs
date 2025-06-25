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

fn ToCharArray(s: String) -> (a: Vec<char>)
    ensures
        a.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i)
{
    return Vec::new();
}

}