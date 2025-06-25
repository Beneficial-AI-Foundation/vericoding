// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Find(blood: Vec<int>, key: int) -> (index: int)
    requires blood != null
    ensures 0 <= index ==> index < blood.len() and blood[index] == key,
            index < 0 ==> forall|k: int| 0 <= k < blood.len() ==> blood[k] != key
{
}

}