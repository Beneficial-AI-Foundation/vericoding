// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: String) -> bool {
    // no b's after non-b's
  forall i, j :: 0 <= i <= j < s.len() && s.spec_index(i) == 'b' && s.spec_index(j) != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < s.len() && s.spec_index(i) != 'd' && s.spec_index(j) == 'd' ==> i < j
}

fn BadSort(a: String) -> (b: String)
    requires
        forall i :: 0<=i<a.len() ==> a.spec_index(i) in
{
    return String::new();
}

}