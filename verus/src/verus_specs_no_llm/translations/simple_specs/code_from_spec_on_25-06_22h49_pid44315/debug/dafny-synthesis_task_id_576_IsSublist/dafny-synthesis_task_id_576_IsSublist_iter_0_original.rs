// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        true <== (exists i :: 0 <= i <= main.len() - sub.len() && sub == main.spec_index(i..i + sub.len()))
{
    return false;
}

}