// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_below_zero(operations: Seq<int>) -> s:array<int>, result:bool
    ensures
        s.len() == operations.len() + 1,
        s.index(0)==0,
        forall |i: int| 0 <= i < s.len()-1 ==> s.index(i+1)==s.index(i)+operations.index(i),
        result == true ==> (exists |i: int| 1 <= i <= operations.len() && s.index(i) < 0),
        result == false ==> forall |i: int| 0 <= i < s.len() ==> s.index(i) >= 0
;

proof fn lemma_below_zero(operations: Seq<int>) -> (s: Vec<int>, result: bool)
    ensures
        s.len() == operations.len() + 1,
        s.index(0)==0,
        forall |i: int| 0 <= i < s.len()-1 ==> s.index(i+1)==s.index(i)+operations.index(i),
        result == true ==> (exists |i: int| 1 <= i <= operations.len() && s.index(i) < 0),
        result == false ==> forall |i: int| 0 <= i < s.len() ==> s.index(i) >= 0
{
    Vec::new()
}

}