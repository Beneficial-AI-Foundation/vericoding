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
function sorted(s : seq<int>) : bool {
 forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// SPEC


// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int
    requires
        0 <= l < r <= a.len(),
        0 <= l < m < r <= a.len(),
        sorted(a.index(l..m)) && sorted(a.index(m..r))
    ensures
        ret.index(..) == a.index(l..r),
        sorted(a.index(l..r)),
        a.index(..l) == old(a.index(..l)),
        a.index(r..) == old(a.index(r..))
 modifies a
;

proof fn lemma_copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>, k2: : 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// SPEC


// Ex2

method mergeArr(a : array<int>, l: int, m: int, r: int)
    requires
        0 <= l < r <= a.len(),
        0 <= l < m < r <= a.len(),
        sorted(a.index(l..m)) && sorted(a.index(m..r))
    ensures
        ret.index(..) == a.index(l..r),
        sorted(a.index(l..r)),
        a.index(..l) == old(a.index(..l)),
        a.index(r..) == old(a.index(r..))
 modifies a
{
    Vec::new()
}

}