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

spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}
spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

fn ToUppercase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> if IsLowerCase(s.spec_index(i)) then IsLowerUpperPair(s.spec_index(i), v.spec_index(i)) else v.spec_index(i) == s.spec_index(i)
{
    return String::new();
}

}