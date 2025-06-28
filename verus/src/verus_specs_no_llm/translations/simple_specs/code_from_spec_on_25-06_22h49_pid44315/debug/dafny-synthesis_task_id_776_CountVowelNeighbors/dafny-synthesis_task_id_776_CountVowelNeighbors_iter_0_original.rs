// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsVowel(c: char) -> bool {
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'
}

fn CountVowelNeighbors(s: String) -> (count: int)
    ensures
        count >= 0,
        count ==  set i: int .len() 1 <= i < s.len()-1 && IsVowel(s.spec_index(i-1)) && IsVowel(s.spec_index(i+1)) |
{
    return 0;
}

}