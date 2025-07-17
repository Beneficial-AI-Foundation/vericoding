// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_BadSort(a: String) -> b: string
    requires
        forall |i: int| 0<=i<a.len() ==> a.index(i) in
;

proof fn lemma_BadSort(a: String) -> (b: String)
    requires
        forall |i: int| 0<=i<a.len() ==> a.index(i) in
{
    String::new()
}

}