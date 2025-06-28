// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn below_zero(operations: Seq<int>) -> (s: Vec<int>, result: bool)
    ensures
        s.len() == operations.len() + 1,
        s.spec_index(0)==0,
        forall i :: 0 <= i < s.len()-1 ==> s.spec_index(i+1)==s.spec_index(i)+operations.spec_index(i),
        result == true ==> (exists i :: 1 <= i <= operations.len() && s.spec_index(i) < 0),
        result == false ==> forall i :: 0 <= i < s.len() ==> s.spec_index(i) >= 0
{
    return Vec::new();
}

}