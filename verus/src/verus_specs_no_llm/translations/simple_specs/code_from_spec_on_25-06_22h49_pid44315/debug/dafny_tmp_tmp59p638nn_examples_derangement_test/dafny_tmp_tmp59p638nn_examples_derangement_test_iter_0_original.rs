// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn derangement(s: Seq<nat>) -> bool {
    forall i :: 0 <= i < s.len() ==> s.spec_index(i) != i
}

}