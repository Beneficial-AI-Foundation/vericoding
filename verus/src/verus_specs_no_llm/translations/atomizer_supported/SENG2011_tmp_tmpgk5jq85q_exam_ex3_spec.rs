// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Symmetric(a: Vec<int>) -> flag: bool
    ensures
        flag == true ==> forall |x: int| 0 <= x < a.len() ==> a.index(x) == a.index(a.len() - x - 1),
        flag == false ==> exists |x: int| 0 <= x < a.len() && a.index(x) != a.index(a.len() - x - 1)
;

proof fn lemma_Symmetric(a: Vec<int>) -> (flag: bool)
    ensures
        flag == true ==> forall |x: int| 0 <= x < a.len() ==> a.index(x) == a.index(a.len() - x - 1),
        flag == false ==> exists |x: int| 0 <= x < a.len() && a.index(x) != a.index(a.len() - x - 1)
{
    false
}

}