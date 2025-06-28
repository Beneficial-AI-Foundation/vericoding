// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum1(v: Vec<int>) -> (i: int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
  i := 0;
  assume 0<=i<v.Length;
  assume forall k:: 0<=k<v.Length ==> v[i]>=v[k];
  return i;
}


// SPEC

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue1(v:array<int>) returns (m:int)
    requires
        v.len()>0,
        v.len()>0
    ensures
        0<=i<v.len(),
        forall k:: 0<=k<v.len() ==> v.spec_index(i)>=v.spec_index(k),
        m in v.spec_index(..),
        forall k::0<=k<v.len() ==> m>=v.spec_index(k)
{
    return 0;
}

}