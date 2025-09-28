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
proof fn exists_even_lemma(lst: &Vec<i32>)
    requires exists|x: i32| lst@.contains(x) && is_even(x)
    ensures exists|i: int| 0 <= i < lst@.len() && is_even(lst@[i])
{
    let x = choose|x: i32| lst@.contains(x) && is_even(x);
    let i = choose|i: int| 0 <= i < lst@.len() && lst@[i] == x;
    assert(is_even(lst@[i]));
}

proof fn exists_odd_lemma(lst: &Vec<i32>)
    requires exists|x: i32| lst@.contains(x) && is_odd(x)
    ensures exists|i: int| 0 <= i < lst@.len() && is_odd(lst@[i])
{
    let x = choose|x: i32| lst@.contains(x) && is_odd(x);
    let i = choose|i: int| 0 <= i < lst@.len() && lst@[i] == x;
    assert(is_odd(lst@[i]));
}

/* helper modified by LLM (iteration 5): fixed return value naming for functions with ensures clauses */
fn is_even_exec(n: i32) -> (result: bool)
    ensures result == is_even(n)
{
    n % 2 == 0
}

fn is_odd_exec(n: i32) -> (result: bool)
    ensures result == is_odd(n)
{
    n % 2 != 0
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
    /* code modified by LLM (iteration 5): added decreases clause for while loop */
    proof {
        exists_even_lemma(lst);
        exists_odd_lemma(lst);
    }
    
    let mut even_val: Option<i32> = None;
    let mut odd_val: Option<i32> = None;
    let mut i = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            even_val.is_some() ==> is_even(even_val.unwrap()),
            odd_val.is_some() ==> is_odd(odd_val.unwrap()),
            even_val.is_some() ==> lst@.contains(even_val.unwrap()),
            odd_val.is_some() ==> lst@.contains(odd_val.unwrap()),
        decreases lst.len() - i
    {
        if even_val.is_none() && is_even_exec(lst[i]) {
            even_val = Some(lst[i]);
        }
        if odd_val.is_none() && is_odd_exec(lst[i]) {
            odd_val = Some(lst[i]);
        }
        if even_val.is_some() && odd_val.is_some() {
            break;
        }
        i += 1;
    }
    
    even_val.unwrap() * odd_val.unwrap()
}
// </vc-code>

}
fn main() {}