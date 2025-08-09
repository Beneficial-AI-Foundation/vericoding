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
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@.index(j) != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    
    i
}

}

fn main() {}