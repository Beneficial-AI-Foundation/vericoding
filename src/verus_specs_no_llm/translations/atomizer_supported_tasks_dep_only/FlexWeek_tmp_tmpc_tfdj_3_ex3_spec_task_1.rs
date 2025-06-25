// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Max(a: Vec<nat>) -> (m: int)
    ensures a.len() > 0 ==> forall|k: int| 0<=k<a.len() ==> m >= a[k]// not strong enough,
            a.len() == 0 ==> m == -1,
            a.len() > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function
{
}

}