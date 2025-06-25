// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn copy(src: Vec<int>, sStart: nat, dest: Vec<int>, dStart: nat, len: nat) -> (r: Vec<int>)
    requires src.len() >= sStart + len,
             dest.len() >= dStart + len
    ensures r.len() == dest.len(),
            r[..dStart] == dest[..dStart],
            r[dStart + len..] == dest[dStart + len..],
            r[dStart..len+dStart] == src[sStart..len+sStart]
{
}

}