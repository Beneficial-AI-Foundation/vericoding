// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>, k2: : 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
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

method sortAux(a : array<int>, l: int, r: int)
    requires
        0 <= l < r <= a.len(),
        0 <= l < m < r <= a.len(),
        sorted(a.spec_index(l..m)) && sorted(a.spec_index(m..r)),
        0 <= l < r <= a.len()
 modifies a
    ensures
        ret.spec_index(..) == a.spec_index(l..r),
        sorted(a.spec_index(l..r)),
        a.spec_index(..l) == old(a.spec_index(..l)),
        a.spec_index(r..) == old(a.spec_index(r..))
 modifies a,
        sorted(a.spec_index(l..r)),
        a.spec_index(..l) == old(a.spec_index(..l)),
        a.spec_index(r..) == old(a.spec_index(r..))
{
    return Vec::new();
}

}