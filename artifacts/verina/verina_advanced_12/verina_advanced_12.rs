use vstd::prelude::*;

verus! {

spec fn first_duplicate_precond(lst: Seq<i32>) -> bool {
    true
}

spec fn first_duplicate_postcond(lst: Seq<i32>, result: i32) -> bool {
    (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&
    (result != -1 ==> exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == result && lst[j] == result)
}

fn first_duplicate(lst: Vec<i32>) -> (result: i32)
    requires first_duplicate_precond(lst@)
{
    for i in 0..lst.len()
        invariant i <= lst.len()
    {
        let current = lst[i];
        for j in 0..i
            invariant j <= i, i < lst.len()
        {
            if lst[j] == current {
                return current;
            }
        }
    }
    -1
}

}

fn main() {}