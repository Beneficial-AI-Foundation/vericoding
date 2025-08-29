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
    let mut n: usize = 0;
    
    while n < a.len()
        invariant
            n <= a.len(),
            forall|i: int| 0 <= i < n ==> a@.index(i) != e,
        decreases a.len() - n,
    {
        if a[n] == e {
            return n;
        }
        n = n + 1;
    }
    
    n
}

}

fn main() {}