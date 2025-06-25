// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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