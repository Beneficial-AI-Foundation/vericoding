// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn notin(y: nat, x: Vec<nat>, x: Seq<nat>) -> bool {
    forall i :: 0 <= i < x.len() ==> y != x.spec_index(i)
}

}