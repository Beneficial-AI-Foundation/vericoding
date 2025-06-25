// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Total(a: Seq<nat>) -> (r: nat)
    ensures r == total (a[0..a.len()]);
{
}

}