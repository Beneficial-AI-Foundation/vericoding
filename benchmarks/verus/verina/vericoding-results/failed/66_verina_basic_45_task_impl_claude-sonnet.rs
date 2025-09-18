// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn find_product_precond(lst: Seq<i32>) -> bool {
    lst.len() > 1 &&
    (exists|x: i32| lst.contains(x) && is_even(x)) &&
    (exists|x: i32| lst.contains(x) && is_odd(x))
}

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}

spec fn first_even_odd_indices(lst: Seq<i32>) -> Option<(int, int)> {
    let even_index = (choose|i: int| 0 <= i < lst.len() && is_even(lst[i]));
    let odd_index = (choose|i: int| 0 <= i < lst.len() && is_odd(lst[i]));
    if (exists|i: int| 0 <= i < lst.len() && is_even(lst[i])) &&
       (exists|i: int| 0 <= i < lst.len() && is_odd(lst[i])) {
        Some((even_index, odd_index))
    } else {
        None
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed is_even to exec mode for runtime usage */
exec fn is_even_exec(n: i32) -> bool {
    n % 2 == 0
}

exec fn is_odd_exec(n: i32) -> bool {
    n % 2 != 0
}

proof fn exists_implies_choose(lst: Seq<i32>)
    ensures
        (exists|i: int| 0 <= i < lst.len() && is_even(lst[i])) ==> {
            let chosen = choose|i: int| 0 <= i < lst.len() && is_even(lst[i]);
            0 <= chosen < lst.len() && is_even(lst[chosen])
        },
        (exists|i: int| 0 <= i < lst.len() && is_odd(lst[i])) ==> {
            let chosen = choose|i: int| 0 <= i < lst.len() && is_odd(lst[i]);
            0 <= chosen < lst.len() && is_odd(lst[chosen])
        }
{
}

proof fn first_even_odd_indices_some(lst: Seq<i32>)
    requires
        exists|x: i32| lst.contains(x) && is_even(x),
        exists|x: i32| lst.contains(x) && is_odd(x),
    ensures
        matches!(first_even_odd_indices(lst), Some(_))
{
}

proof fn contains_implies_index_exists(lst: Seq<i32>, x: i32)
    requires
        lst.contains(x)
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == x
{
}
// </vc-helpers>

// <vc-spec>
fn find_product(lst: &Vec<i32>) -> (result: i32)
    requires 
        lst.len() > 1,
        exists|x: i32| lst@.contains(x) && is_even(x),
        exists|x: i32| lst@.contains(x) && is_odd(x),
    ensures
        match first_even_odd_indices(lst@) {
            Some((ei, oi)) => result == lst@[ei] * lst@[oi],
            None => true,
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use exec mode functions for runtime checks */
    proof {
        exists_implies_choose(lst@);
        first_even_odd_indices_some(lst@);
    }
    
    let mut even_idx: usize = 0;
    let mut odd_idx: usize = 0;
    let mut found_even = false;
    let mut found_odd = false;
    
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            found_even ==> (0 <= even_idx < lst.len() && is_even(lst@[even_idx as int])),
            found_odd ==> (0 <= odd_idx < lst.len() && is_odd(lst@[odd_idx as int])),
            !found_even ==> (forall|j: int| 0 <= j < i ==> !is_even(lst@[j])),
            !found_odd ==> (forall|j: int| 0 <= j < i ==> !is_odd(lst@[j])),
        decreases lst.len() - i
    {
        if !found_even && is_even_exec(lst[i]) {
            even_idx = i;
            found_even = true;
        }
        if !found_odd && is_odd_exec(lst[i]) {
            odd_idx = i;
            found_odd = true;
        }
        if found_even && found_odd {
            break;
        }
        i += 1;
    }
    
    lst[even_idx] * lst[odd_idx]
}
// </vc-code>

}
fn main() {}