// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mmaximum2(v: Vec<int>) -> i:int) 
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

method mmaxvalue2(v:array<int>) returns (m:int
    requires
        v.len()>0,
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k),
        m in v.index(..),
        forall |k: int|0<=k<v.len() ==> m>=v.index(k)
;

proof fn lemma_mmaximum2(v: Vec<int>) -> (i: int) 
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

method mmaxvalue2(v:array<int>) returns (m:int)
    requires
        v.len()>0,
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k),
        m in v.index(..),
        forall |k: int|0<=k<v.len() ==> m>=v.index(k)
{
    0
}

}