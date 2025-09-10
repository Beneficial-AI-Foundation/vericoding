use vstd::prelude::*;

verus! {

spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
{
    assume(false);
    unreached()
}

}
fn main() {}