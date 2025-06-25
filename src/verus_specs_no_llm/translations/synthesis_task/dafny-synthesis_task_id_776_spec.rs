// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsVowel(c: char) -> bool {
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'
}

fn CountVowelNeighbors(s: String) -> (count: int)
    ensures count >= 0,
            count ==  set i: int .len() 1 <= i < s.len()-1 and IsVowel(s[i-1]) and IsVowel(s[i+1]) |
{
}

}