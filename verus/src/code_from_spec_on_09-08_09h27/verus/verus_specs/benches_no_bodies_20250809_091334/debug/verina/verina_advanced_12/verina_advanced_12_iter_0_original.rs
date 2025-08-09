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
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {}