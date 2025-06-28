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
spec fn IsLowerCase(c: char) -> bool {
    97 <= c as int <= 122
}
spec fn IsLowerUpperPair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

fn ToggleCase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> if IsLowerCase(s.spec_index(i)) then IsLowerUpperPair(s.spec_index(i), v.spec_index(i)) else if IsUpperCase(s.spec_index(i)) then IsUpperLowerPair(s.spec_index(i), v.spec_index(i)) else v.spec_index(i) == s.spec_index(i)
{
    return String::new();
}

}