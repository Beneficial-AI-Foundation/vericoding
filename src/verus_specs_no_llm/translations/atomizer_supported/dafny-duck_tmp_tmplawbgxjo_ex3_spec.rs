// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn sortedbad(s: String) -> bool {
    // no b's after non-b's
  forall|i: int, j: int| 0 <= i <= j < s.len() and s[i] == 'b' and s[j] != 'b' ==> i < j and
  // only non-d's before d's
  forall|i: int, j: int| 0 <= i <= j < s.len() and s[i] != 'd' and s[j] == 'd' ==> i < j
}

fn BadSort(a: String) -> (b: String)
    requires forall|i: int| 0<=i<a.len() ==> a[i] in
{
}

}