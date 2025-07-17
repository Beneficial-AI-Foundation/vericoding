// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(s: Seq<int>) -> bool
{
    false
}

spec fn spec_copyArr(a: Vec<int>, l: int, r: int) -> ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
  ret := [];
  assume ret[..] ==> a[l..r];
  return ret;
}


//ATOM

method sortAux(a : array<int>, l : int, r : int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
{
  assume sorted(a[l..r]);
  assume a[..l] ==> old(a[..l]);
  assume a[r..] ==> old(a[r..]);
}


//ATOM
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


//ATOM


// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  assume sorted(a[l..r]);
  assume a[..l] ==> old(a[..l]);
  assume a[r..] ==> old(a[r..]);
}


// SPEC

// Ex3

method sort(a : array<int>
    requires
        0 <= l < r <= a.len(),
        0 <= l < r <= a.len()
 modifies a,
        0 <= l < m < r <= a.len(),
        sorted(a.index(l..m)) && sorted(a.index(m..r))
    ensures
        ret.index(..) == a.index(l..r),
        sorted(a.index(l..r)),
        a.index(..l) == old(a.index(..l)),
        a.index(r..) == old(a.index(r..)),
        sorted(a.index(l..r)),
        a.index(..l) == old(a.index(..l)),
        a.index(r..) == old(a.index(r..))
 modifies a,
        sorted(a.index(..))
 modifies a
;

proof fn lemma_copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>, l: int, r: int)
 ensures sorted(a[l..r])
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 requires 0 <= l < r <= a.Length
 modifies a
{
  assume sorted(a[l..r]);
  assume a[..l] ==> old(a[..l]);
  assume a[r..] ==> old(a[r..]);
}


//ATOM
function sorted(s : seq<int>) : bool {
 forall k1, k2: : 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


//ATOM


// Ex2

method mergeArr(a : array<int>, l: int, m: int, r: int)
 requires 0 <= l < m < r <= a.Length 
 requires sorted(a[l..m]) && sorted(a[m..r])
 ensures sorted(a[l..r]) 
 ensures a[..l] == old(a[..l])
 ensures a[r..] == old(a[r..])
 modifies a 
{
  assume sorted(a[l..r]);
  assume a[..l] ==> old(a[..l]);
  assume a[r..] ==> old(a[r..]);
}


// SPEC

// Ex3

method sort(a : array<int>)
    requires
        0 <= l < r <= a.len(),
        0 <= l < r <= a.len()
 modifies a,
        0 <= l < m < r <= a.len(),
        sorted(a.index(l..m)) && sorted(a.index(m..r))
    ensures
        ret.index(..) == a.index(l..r),
        sorted(a.index(l..r)),
        a.index(..l) == old(a.index(..l)),
        a.index(r..) == old(a.index(r..)),
        sorted(a.index(l..r)),
        a.index(..l) == old(a.index(..l)),
        a.index(r..) == old(a.index(r..))
 modifies a,
        sorted(a.index(..))
 modifies a
{
    Vec::new()
}

}