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
    let mut result = dest.clone();
    let mut i: nat = 0;
    
    while i < len
        invariant
            i <= len,
            result.len() == dest.len(),
            result.spec_index(..dStart) == dest.spec_index(..dStart),
            result.spec_index(dStart + len..) == dest.spec_index(dStart + len..),
            forall |j: int| 0 <= j < i ==> result.spec_index(dStart + j) == src.spec_index(sStart + j)
    {
        assert(sStart + i < src.len());
        assert(dStart + i < result.len());
        result.set(dStart + i, src[sStart + i]);
        i = i + 1;
    }
    
    result
}

}