// Translated from Dafny
use builtin::*;
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

spec fn ShiftMinus32(c: char) -> char
{
    '\0'
}

spec fn spec_ToUppercase(s: String) -> v: string
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==>  if IsLowerCase(s.index(i)) then IsLowerUpperPair(s.index(i), v.index(i)) else v.index(i) == s.index(i)
;

proof fn lemma_ToUppercase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==>  if IsLowerCase(s.index(i)) then IsLowerUpperPair(s.index(i), v.index(i)) else v.index(i) == s.index(i)
{
    String::new()
}

}