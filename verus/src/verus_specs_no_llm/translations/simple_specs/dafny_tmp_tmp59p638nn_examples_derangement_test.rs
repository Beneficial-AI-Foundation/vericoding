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

spec fn derangement(s: Seq<nat>) -> bool {
    forall i :: 0 <= i < s.len() ==> s.spec_index(i) != i
}

}