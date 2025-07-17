// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Find(blood: Vec<int>, key: int) -> index: int
    requires
        blood != null
    ensures
        0 <= index ==> index < blood.len() && blood.index(index) == key,
        index < 0 ==> forall |k: int| 0 <= k < blood.len() ==> blood.index(k) != key
;

proof fn lemma_Find(blood: Vec<int>, key: int) -> (index: int)
    requires
        blood != null
    ensures
        0 <= index ==> index < blood.len() && blood.index(index) == key,
        index < 0 ==> forall |k: int| 0 <= k < blood.len() ==> blood.index(k) != key
{
    0
}

}