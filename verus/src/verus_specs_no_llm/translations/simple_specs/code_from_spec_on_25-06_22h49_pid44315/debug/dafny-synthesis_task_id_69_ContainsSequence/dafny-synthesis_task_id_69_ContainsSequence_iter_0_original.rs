// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsSequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < list.len() && sub == list.spec_index(i))
{
    return false;
}

}