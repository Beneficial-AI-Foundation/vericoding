// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures
        result <==> exists n: nat :: n <= ops.len() && sum(ops, n) < 0
{
    return false;
}

}