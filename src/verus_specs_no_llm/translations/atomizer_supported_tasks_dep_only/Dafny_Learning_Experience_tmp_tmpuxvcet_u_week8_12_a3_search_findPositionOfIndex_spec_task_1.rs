// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindPositionOfElement(a: Vec<int>, Element: nat, n1: nat, s1: Seq<int>) -> Position: int, Count: nat
    requires n1 == s1.len() and 0 <= n1 <= a.len(),
             forall|i: int| 0<= i < s1.len() ==> a[i] == s1[i]
    ensures Position == -1 or Position >= 1,
            s1.len() != 0 and Position >= 1 ==> exists|i: int| 0 <= i < s1.len() and s1[i] == Element
{
}

}