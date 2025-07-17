// Translated from Dafny
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

spec fn Shift32(c: char) -> char
{
    '\0'
}

spec fn spec_ToLowercase(s: String) -> v: string
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==>  if IsUpperCase(s.index(i)) then IsUpperLowerPair(s.index(i), v.index(i)) else v.index(i) == s.index(i)
;

proof fn lemma_ToLowercase(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==>  if IsUpperCase(s.index(i)) then IsUpperLowerPair(s.index(i), v.index(i)) else v.index(i) == s.index(i)
{
    String::new()
}

}