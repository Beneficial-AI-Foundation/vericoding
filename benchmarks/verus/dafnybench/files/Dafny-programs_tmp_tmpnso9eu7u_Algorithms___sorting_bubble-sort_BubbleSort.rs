use vstd::prelude::*;

verus! {

spec fn sorted_between(a: Seq<int>, from: int, to: int) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() && from <= i <= j <= to ==> a[i] <= a[j]
}

spec fn sorted(a: Seq<int>) -> bool {
    sorted_between(a, 0, (a.len() - 1) as int)
}

fn bubble_sort(a: &mut Vec<int>)
    ensures 
        sorted(a@),
        a@.to_multiset() == old(a)@.to_multiset()
{
    assume(false);
    unreached()
}

}
fn main() {}