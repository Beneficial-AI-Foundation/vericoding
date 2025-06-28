// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsK(s: Seq<int>, k: int) -> (result: bool)
    ensures
        result <==> k in s
{
    return false;
}

}