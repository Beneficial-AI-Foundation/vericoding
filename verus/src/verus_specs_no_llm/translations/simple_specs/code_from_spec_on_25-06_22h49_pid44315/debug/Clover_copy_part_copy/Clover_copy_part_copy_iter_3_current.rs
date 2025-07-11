use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn copy(src: Vec<int>, sStart: nat, dest: Vec<int>, dStart: nat, len: nat) -> (r: Vec<int>)
    requires
        src.len() >= sStart + len,
        dest.len() >= dStart + len
    ensures
        r.len() == dest.len(),
        r.spec_index(..dStart) == dest.spec_index(..dStart),
        r.spec_index(dStart + len..) == dest.spec_index(dStart + len..),
        r.spec_index(dStart..dStart+len) == src.spec_index(sStart..sStart+len)
{
    let mut result = Vec::new();
    let mut k: nat = 0;
    
    // First, copy the initial part of dest
    while k < dStart
        invariant
            k <= dStart,
            result.len() == k,
            forall |j: int| 0 <= j < k ==> result.spec_index(j) == dest.spec_index(j)
    {
        result.push(dest[k]);
        k = k + 1;
    }
    
    // Then copy from src
    let mut i: nat = 0;
    while i < len
        invariant
            i <= len,
            result.len() == dStart + i,
            forall |j: int| 0 <= j < dStart ==> result.spec_index(j) == dest.spec_index(j),
            forall |j: int| 0 <= j < i ==> result.spec_index(dStart + j) == src.spec_index(sStart + j)
    {
        assert(sStart + i < src.len());
        result.push(src[sStart + i]);
        i = i + 1;
    }
    
    // Finally, copy the remaining part of dest
    let mut m: nat = dStart + len;
    while m < dest.len()
        invariant
            m >= dStart + len,
            m <= dest.len(),
            result.len() == m,
            forall |j: int| 0 <= j < dStart ==> result.spec_index(j) == dest.spec_index(j),
            forall |j: int| 0 <= j < len ==> result.spec_index(dStart + j) == src.spec_index(sStart + j),
            forall |j: int| dStart + len <= j < m ==> result.spec_index(j) == dest.spec_index(j)
    {
        result.push(dest[m]);
        m = m + 1;
    }
    
    result
}

}