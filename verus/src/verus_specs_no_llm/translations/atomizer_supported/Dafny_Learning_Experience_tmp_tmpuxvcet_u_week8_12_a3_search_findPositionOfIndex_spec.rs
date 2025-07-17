// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindPositionOfElement(a: Vec<int>, Element: nat, n1: nat, s1: Seq<int>) -> Position:int,Count:nat
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall |i: int| 0<= i < s1.len() ==> a.index(i) == s1.index(i)
    ensures
        Position == -1 || Position >= 1,
        s1.len() != 0 && Position >= 1 ==> exists |i: int| 0 <= i < s1.len() && s1.index(i) == Element
;

proof fn lemma_FindPositionOfElement(a: Vec<int>, Element: nat, n1: nat, s1: Seq<int>) -> (Position: int, Count: nat)
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall |i: int| 0<= i < s1.len() ==> a.index(i) == s1.index(i)
    ensures
        Position == -1 || Position >= 1,
        s1.len() != 0 && Position >= 1 ==> exists |i: int| 0 <= i < s1.len() && s1.index(i) == Element
{
    (0, 0)
}

}