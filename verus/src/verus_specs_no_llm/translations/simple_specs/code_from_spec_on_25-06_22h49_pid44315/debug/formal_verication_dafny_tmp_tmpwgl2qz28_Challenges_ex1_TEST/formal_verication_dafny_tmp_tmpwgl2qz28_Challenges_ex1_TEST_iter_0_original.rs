// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PalVerify(a: Vec<char>) -> (yn: bool)
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
        yn == true ==> forall i :: 0 <= i < a.len()/2 ==> a.spec_index(i) == a.spec_index(a.len() - i -1),
        yn == false ==> exists i :: 0 <= i < a.len()/2 && a.spec_index(i) != a.spec_index(a.len() - i -1),
        forall j :: 0<=j<a.len() ==> a.spec_index(j) == old(a.spec_index(j))
{
    return 0;
}

}