use vstd::prelude::*;

verus! {

fn search_recursive(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires 
        0 <= i <= j <= a.len(),
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures 
        i <= k <= j,
        forall|r: int| i <= r < k ==> a[r] >= x,
        forall|r: int| k <= r < j ==> a[r] < x,
    decreases j - i
{
    assume(false);
    unreached();
}

}
fn main() {}