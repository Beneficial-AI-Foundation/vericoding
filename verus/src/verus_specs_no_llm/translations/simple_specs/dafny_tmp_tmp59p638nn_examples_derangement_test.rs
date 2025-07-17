// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn derangement(s: Seq<nat>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s.index(i) != i
}

spec fn multisetRange(n: nat) -> multiset<nat>
{
    0
}

}