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
spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists i,j :: 0 <= i < j < q.len() && q.spec_index(i) + q.spec_index(j) == x
}

}