use vstd::prelude::*;

verus! {

pub fn IsSorted(a: &[i32]) -> (isSorted: bool)
    ensures
        isSorted <==> forall|j: int| 1 <= j < a.len() ==> a[j as int - 1] <= a[j as int]
{
}

}