// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceBlanksWithChar(s: String, ch: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> (s.spec_index(i) == ' ' ==> v.spec_index(i) == ch) && (s.spec_index(i) != ' ' ==> v.spec_index(i) == s.spec_index(i))
{
    return String::new();
}

}