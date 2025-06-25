// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}
spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

fn ToUppercase(s: String) -> (v: String)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
}

}