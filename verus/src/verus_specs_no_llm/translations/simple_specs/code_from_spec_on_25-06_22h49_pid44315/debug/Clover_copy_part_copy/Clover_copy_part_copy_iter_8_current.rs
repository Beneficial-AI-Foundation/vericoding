use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn copy(src: Vec<usize>, sStart: nat, dest: Vec<usize>, dStart: nat, len: nat) -> (r: Vec<usize>)
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
    let mut k: usize = 0;
    let dStart_usize = dStart as usize;
    let len_usize = len as usize;
    let sStart_usize = sStart as usize;
    
    // First, copy the initial part of dest
    while k < dStart_usize
        invariant
            k <= dStart_usize,
            dStart_usize == dStart,
            result.len() == k,
            k <= dest.len(),
            forall |j: int| 0 <= j < k ==> result.spec_index(j) == dest.spec_index(j)
    {
        result.push(dest[k]);
        k = k + 1;
    }
    
    // Then copy from src
    let mut i: usize = 0;
    while i < len_usize
        invariant
            i <= len_usize,
            len_usize == len,
            sStart_usize == sStart,
            dStart_usize == dStart,
            result.len() == dStart_usize + i,
            sStart_usize + i <= src.len(),
            dStart_usize + len_usize <= dest.len(),
            forall |j: int| 0 <= j < dStart ==> result.spec_index(j) == dest.spec_index(j),
            forall |j: int| 0 <= j < i ==> result.spec_index(dStart + j) == src.spec_index(sStart + j)
    {
        result.push(src[sStart_usize + i]);
        i = i + 1;
    }
    
    // Finally, copy the remaining part of dest
    let mut m: usize = dStart_usize + len_usize;
    while m < dest.len()
        invariant
            m >= dStart_usize + len_usize,
            m <= dest.len(),
            dStart_usize == dStart,
            len_usize == len,
            sStart_usize == sStart,
            dStart_usize + len_usize == dStart + len,
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