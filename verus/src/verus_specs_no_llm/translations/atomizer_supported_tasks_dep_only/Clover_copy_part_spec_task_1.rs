// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_copy(src: Vec<int>, sStart: nat, dest: Vec<int>, dStart: nat, len: nat) -> r: array<int>
    requires
        src.len() >= sStart + len,
        dest.len() >= dStart + len
    ensures
        r.len() == dest.len(),
        r.index(..dStart) == dest.index(..dStart),
        r.index(dStart + len..) == dest.index(dStart + len..),
        r.index(dStart..len+dStart) == src.index(sStart..len+sStart)
;

proof fn lemma_copy(src: Vec<int>, sStart: nat, dest: Vec<int>, dStart: nat, len: nat) -> (r: Vec<int>)
    requires
        src.len() >= sStart + len,
        dest.len() >= dStart + len
    ensures
        r.len() == dest.len(),
        r.index(..dStart) == dest.index(..dStart),
        r.index(dStart + len..) == dest.index(dStart + len..),
        r.index(dStart..len+dStart) == src.index(sStart..len+sStart)
{
    Vec::new()
}

}