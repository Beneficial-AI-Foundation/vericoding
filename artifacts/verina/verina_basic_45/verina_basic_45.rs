use vstd::prelude::*;

verus! {

// Helper functions equivalent to Lean's isEven/isOdd
spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}

// Precondition equivalent to Lean's findProduct_precond
spec fn find_product_precond(lst: &Vec<i32>) -> bool {
    lst.len() > 1 &&
    (exists |x: i32| #![auto] lst@.contains(x) && is_even(x)) &&
    (exists |x: i32| #![auto] lst@.contains(x) && is_odd(x))
}

// Postcondition equivalent to Lean's findProduct_postcond  
spec fn find_product_postcond(lst: &Vec<i32>, result: i32) -> bool {
    // If both even and odd elements exist, result should be their product
    if (exists |x: i32| #![auto] lst@.contains(x) && is_even(x)) &&
       (exists |x: i32| #![auto] lst@.contains(x) && is_odd(x)) {
        exists |ei: int, oi: int| #![auto]
            0 <= ei < lst.len() && 0 <= oi < lst.len() &&
            is_even(lst[ei]) && is_odd(lst[oi]) &&
            result == lst[ei] * lst[oi]
    } else {
        true
    }
}

// Find first even index
fn find_first_even_index(lst: &Vec<i32>) -> (result: Option<usize>)
    ensures match result {
        Some(i) => i < lst.len() && is_even(lst[i as int]),
        None => true,
    }
{
    for i in 0..lst.len() {
        if lst[i] % 2 == 0 {
            return Some(i);
        }
    }
    None
}

// Find first odd index
fn find_first_odd_index(lst: &Vec<i32>) -> (result: Option<usize>)
    ensures match result {
        Some(i) => i < lst.len() && is_odd(lst[i as int]),
        None => true,
    }
{
    for i in 0..lst.len() {
        if lst[i] % 2 != 0 {
            return Some(i);
        }
    }
    None
}

// Combined function equivalent to Lean's firstEvenOddIndices
fn first_even_odd_indices(lst: &Vec<i32>) -> (result: Option<(usize, usize)>)
    ensures match result {
        Some((ei, oi)) => ei < lst.len() && oi < lst.len() && 
                         is_even(lst[ei as int]) && is_odd(lst[oi as int]),
        None => true,
    }
{
    let even_index = find_first_even_index(lst);
    let odd_index = find_first_odd_index(lst);
    
    match (even_index, odd_index) {
        (Some(ei), Some(oi)) => Some((ei, oi)),
        _ => None,
    }
}

// Main function equivalent to Lean's findProduct
fn find_product(lst: &Vec<i32>) -> (result: i32)  
    requires 
        find_product_precond(lst) &&
        (forall |i: int| #![trigger lst[i]] 0 <= i < lst.len() ==> -1000 <= lst[i] <= 1000),
    ensures find_product_postcond(lst, result)
{
    match first_even_odd_indices(lst) {
        Some((ei, oi)) => lst[ei] * lst[oi],
        None => 0,
    }
}

}

fn main() {}