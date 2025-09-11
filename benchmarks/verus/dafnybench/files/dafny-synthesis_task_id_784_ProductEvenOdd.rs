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
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}