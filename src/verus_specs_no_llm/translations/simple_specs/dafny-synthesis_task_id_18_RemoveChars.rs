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

fn RemoveChars(s1: String, s2: String) -> (v: String)
    ensures
        v.len() <= s1.len(),
        forall i :: 0 <= i < v.len() ==> (v.spec_index(i) in s1) && !(v.spec_index(i) in s2),
        forall i :: 0 <= i < s1.len() ==> (s1.spec_index(i) in s2) || (s1.spec_index(i) in v)
{
    return String::new();
}

}