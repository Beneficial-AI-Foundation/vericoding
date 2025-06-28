use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Empty main function is valid
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < q.len() && 0 <= j < q.len() && i <= j ==> q.spec_index(i) <= q.spec_index(j)
}

}