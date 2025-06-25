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

fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>, k2: : 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// SPEC


// Ex2

method mergeArr(a : array<int>, l: int, m: int, r: int)
    requires
        0 <= l < r <= a.len(),
        0 <= l < m < r <= a.len(),
        sorted(a.spec_index(l..m)) && sorted(a.spec_index(m..r))
    ensures
        ret.spec_index(..) == a.spec_index(l..r),
        sorted(a.spec_index(l..r)),
        a.spec_index(..l) == old(a.spec_index(..l)),
        a.spec_index(r..) == old(a.spec_index(r..))
 modifies a
{
    return Vec::new();
}

}