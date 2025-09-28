// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

spec fn is_first_even(even_index: int, lst: Seq<int>) -> bool
    recommends 0 <= even_index < lst.len() && is_even(lst[even_index])
{
    forall|i: int| 0 <= i < even_index ==> is_odd(lst[i])
}

spec fn is_first_odd(odd_index: int, lst: Seq<int>) -> bool
    recommends 0 <= odd_index < lst.len() && is_odd(lst[odd_index])
{
    forall|i: int| 0 <= i < odd_index ==> is_even(lst[i])
}

fn first_even_odd_indices(lst: Seq<int>) -> (r: (usize, usize))
    requires lst.len() >= 2,
             (exists|i: int| 0 <= i < lst.len() && is_even(lst[i])),
             (exists|i: int| 0 <= i < lst.len() && is_odd(lst[i])),
    ensures ({
        let (even_index, odd_index) = r;
        &&& 0 <= even_index < lst.len()
        &&& 0 <= odd_index < lst.len()
        &&& is_even(lst[even_index as int]) && is_first_even(even_index as int, lst)
        &&& is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst)
    }),
{
  assume(false);
  (0, 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed signature to use Vec<i32> and fixed body logic */
fn find_first_even_index(lst: &Vec<i32>) -> (even_index: usize)
    requires
        exists|i: int| 0 <= i < lst@.len() && is_even(lst@[i] as int),
    ensures
        0 <= even_index < lst@.len(),
        is_even(lst@[even_index as int] as int),
        is_first_even(even_index as int, lst@.map(|_idx, v| v as int)),
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < (i as int) ==> is_odd(lst@[j] as int),
            exists|k: int| (i as int) <= k < lst@.len() && is_even(lst@[k] as int),
        decreases lst.len() - i
    {
        if lst[i] % 2 == 0 {
            return i;
        }
        i = i + 1;
    }
    unreachable!();
}

/* helper modified by LLM (iteration 5): changed signature to use Vec<i32> and fixed body logic */
fn find_first_odd_index(lst: &Vec<i32>) -> (odd_index: usize)
    requires
        exists|i: int| 0 <= i < lst@.len() && is_odd(lst@[i] as int),
    ensures
        0 <= odd_index < lst@.len(),
        is_odd(lst@[odd_index as int] as int),
        is_first_odd(odd_index as int, lst@.map(|_idx, v| v as int)),
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < (i as int) ==> is_even(lst@[j] as int),
            exists|k: int| (i as int) <= k < lst@.len() && is_odd(lst@[k] as int),
        decreases lst.len() - i
    {
        if lst[i] % 2 != 0 {
            return i;
        }
        i = i + 1;
    }
    unreachable!();
}
// </vc-helpers>

// <vc-spec>
fn product_even_odd(lst: Seq<int>) -> (product: i32)
    requires 
        lst.len() >= 2,
        exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
        exists|i: int| 0 <= i < lst.len() && is_odd(lst[i])
    ensures exists|i: int, j: int| 0 <= i < lst.len() && is_even(lst[i]) && is_first_even(i, lst) && 
                                   0 <= j < lst.len() && is_odd(lst[j])  && is_first_odd(j, lst) && product as int == lst[i] * lst[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): call helpers and compute product, assuming executable types */
{
    let even_index = find_first_even_index(lst);
    let odd_index = find_first_odd_index(lst);
    let product = lst[even_index] * lst[odd_index];
    product
}
// </vc-code>

}
fn main() {}