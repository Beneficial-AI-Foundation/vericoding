// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsPalindrome(x: Seq<char>) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < x.len() ==> x[i] == x[x.len() - i - 1])
{
}

}