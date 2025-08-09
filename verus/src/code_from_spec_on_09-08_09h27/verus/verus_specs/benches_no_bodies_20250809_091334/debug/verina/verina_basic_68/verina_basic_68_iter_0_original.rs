use vstd::prelude::*;

verus! {

spec fn linear_search_precond(a: Seq<i32>, e: i32) -> bool {
    true
}

spec fn linear_search_postcond(a: Seq<i32>, e: i32, result: usize) -> bool {
    result <= a.len() &&
    (result == a.len() || a.index(result as int) == e) &&
    (forall|i: int| 0 <= i < result ==> a.index(i) != e)
}

fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires
        linear_search_precond(a@, e),
    ensures
        linear_search_postcond(a@, e, result),
{
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {}