use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

}