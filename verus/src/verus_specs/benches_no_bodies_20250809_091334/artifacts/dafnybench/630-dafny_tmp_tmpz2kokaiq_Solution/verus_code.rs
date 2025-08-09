use vstd::prelude::*;

verus! {
    spec fn sorted(a: &[int]) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    }

    fn binary_search(a: &[int], x: int) -> (index: i32)
        requires sorted(a),
        ensures 
            (0 <= index < a.len()) ==> a[index as int] == x,
            (index == -1) ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}