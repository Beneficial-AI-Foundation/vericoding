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
proof fn find_even_odd_indices(lst: Seq<i32>) -> (ei: int, oi: int)
    requires
        lst.len() > 1,
        (exists|x: i32| lst.contains(x) && is_even(x)),
        (exists|x: i32| lst.contains(x) && is_odd(x))
    ensures
        0 <= ei < lst.len(),
        is_even(lst[ei]),
        0 <= oi < lst.len(),
        is_odd(lst[oi])
{
    let ei = (choose|i: int| 0 <= i < lst.len() && is_even(lst[i]));
    let oi = (choose|i: int| 0 <= i < lst.len() && is_odd(lst[i]));
    (ei, oi)
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
    /* code modified by LLM (iteration 5): Fixed compilation error in proof function call */
    proof {
        let (ei, oi) = find_even_odd_indices(lst@);
    }
    
    let mut even_val: i32 = 0;
    let mut odd_val: i32 = 0;
    
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            i > 0 ==> (even_val != 0 || odd_val != 0),
            even_val != 0 ==> is_even(even_val),
            odd_val != 0 ==> is_odd(odd_val)
        decreases lst.len() - i
    {
        if is_even(lst[i]) && even_val == 0 {
            even_val = lst[i];
        }
        if is_odd(lst[i]) && odd_val == 0 {
            odd_val = lst[i];
        }
        if even_val != 0 && odd_val != 0 {
            break;
        }
        i += 1;
    }
    
    even_val * odd_val
}
// </vc-code>

}
fn main() {}