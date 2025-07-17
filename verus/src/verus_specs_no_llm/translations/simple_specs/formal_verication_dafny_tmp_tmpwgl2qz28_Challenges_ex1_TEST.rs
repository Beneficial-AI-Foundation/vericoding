// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_PalVerify(a: Vec<char>) -> yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
  yn := false;
  assume yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1];
  assume yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1];
  assume forall j :: 0<=j<a.Length ==> a[j] == old(a[j]);
  return yn;
}


// SPEC

method TEST(
    ensures
        yn == true ==> forall |i: int| 0 <= i < a.len()/2 ==> a.index(i) == a.index(a.len() - i -1),
        yn == false ==> exists |i: int| 0 <= i < a.len()/2 && a.index(i) != a.index(a.len() - i -1),
        forall |j: int| 0<=j<a.len() ==> a.index(j) == old(a.index(j))
;

proof fn lemma_PalVerify(a: Vec<char>) -> (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
  yn := false;
  assume yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1];
  assume yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1];
  assume forall j :: 0<=j<a.Length ==> a[j] == old(a[j]);
  return yn;
}


// SPEC

method TEST()
    ensures
        yn == true ==> forall |i: int| 0 <= i < a.len()/2 ==> a.index(i) == a.index(a.len() - i -1),
        yn == false ==> exists |i: int| 0 <= i < a.len()/2 && a.index(i) != a.index(a.len() - i -1),
        forall |j: int| 0<=j<a.len() ==> a.index(j) == old(a.index(j))
{
    0
}

}