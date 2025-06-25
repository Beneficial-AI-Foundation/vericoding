// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}
spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int <= 90
}
spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}
spec fn IsUpperLowerPair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

fn ToggleCase(s: String) -> (v: String)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
}

}