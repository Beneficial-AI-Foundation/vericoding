// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn isPalindrome(s: Vec<char>) -> (result: bool)
    requires 1<= s.len() <= 200000
    ensures result <==> (forall|i: int| 0 <= i < s.len() / 2 ==> s[i] == s[s.len() - 1 - i])
{
}

}