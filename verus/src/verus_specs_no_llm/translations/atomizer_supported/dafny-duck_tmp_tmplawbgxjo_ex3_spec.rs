// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: String) -> bool {
    // no b's after non-b's
  forall |i: int, j: int| 0 <= i <= j < s.len() && s.index(i) == 'b' && s.index(j) != 'b' ==> i < j &&
  // only non-d's before d's
  forall |i: int, j: int| 0 <= i <= j < s.len() && s.index(i) != 'd' && s.index(j) == 'd' ==> i < j
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