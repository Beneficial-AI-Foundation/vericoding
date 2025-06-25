// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists n: nat :: n <= ops.len() and sum(ops, n) < 0
{
}

}