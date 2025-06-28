// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}

}