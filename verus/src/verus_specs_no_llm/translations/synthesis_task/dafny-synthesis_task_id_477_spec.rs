// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}
spec fn IsUpperLowerPair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

fn ToLowercase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==>  if IsUpperCase(s.spec_index(i)) then IsUpperLowerPair(s.spec_index(i), v.spec_index(i)) else v.spec_index(i) == s.spec_index(i)
{
    return String::new();
}

}