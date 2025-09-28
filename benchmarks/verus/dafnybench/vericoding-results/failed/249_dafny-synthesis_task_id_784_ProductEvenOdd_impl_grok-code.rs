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
    requires exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
    requires exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]),
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

// <vc-helpers>
fn first_even_odd_indices(lst: Seq<int>) -> (r: (usize, usize))
    requires lst.len() >= 2,
    requires exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
    requires exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]),
    ensures ({
        let (even_index, odd_index) = r;
        &&& 0 <= even_index < lst.len()
        &&& 0 <= odd_index < lst.len()
        &&& is_even(lst[even_index as int]) && is_first_even(even_index as int, lst)
        &&& is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst)
    }),
{
    let mut even_index: int = 0;
    let mut odd_index: int = 0;
    let mut i: int = 0;

    // Find first even
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|k: int| 0 <= k < i ==> is_odd(lst[k]),
    {
        if lst[i] % 2 == 0 {
            even_index = i;
            proof {
                assert(i >= 0 && i < lst.len());
                assert(is_even(lst[i]));
                assert(forall|k: int| 0 <= k < i ==> is_odd(lst[k]));
                assert(is_first_even(i, lst));
            }
            break;
        }
        i = i + 1;
    }

    i = 0;
    // Find first odd
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|k: int| 0 <= k < i ==> is_even(lst[k]),
    {
        if lst[i] % 2 != 0 {
            odd_index = i;
            proof {
                assert(i >= 0 && i < lst.len());
                assert(is_odd(lst[i]));
                assert(forall|k: int| 0 <= k < i ==> is_even(lst[k]));
                assert(is_first_odd(i, lst));
            }
            break;
        }
        i = i + 1;
    }

    (even_index as usize, odd_index as usize)
}
// </vc-helpers>

// <vc-spec>
fn product_even_odd(lst: Seq<int>) -> (product: i32)
    requires lst.len() >= 2,
    requires exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
    requires exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]),
    ensures exists|i: int, j: int| 0 <= i < lst.len() && is_even(lst[i]) && is_first_even(i, lst) && 
                                   0 <= j < lst.len() && is_odd(lst[j])  && is_first_odd(j, lst) && product as int == lst[i] * lst[j],
// </vc-spec>
// <vc-code>
{
    let tmp = first_even_odd_indices(lst);
    let ei = tmp.0;
    let oi = tmp.1;
    let val1 = lst[ei as int];
    let val2 = lst[oi as int];
    let prod_i64 = (val1 as i64) * (val2 as i64);
    proof {
        let i: int = ei as int;
        let j: int = oi as int;
        assert(0 <= i < lst.len() && 0 <= j < lst.len());
        assert(is_even(lst[i]) && is_first_even(i, lst));
        assert(is_odd(lst[j]) && is_first_odd(j, lst));
        assert(prod_i64 == (lst[i] * lst[j]) as i64);
        assert(prod_i64 >= i32::MIN as i64 && prod_i64 <= i32::MAX as i64);
        assert exists|i_: int, j_: int| 0 <= i_ < lst.len() && is_even(lst[i_]) && is_first_even(i_, lst) &&
                                   0 <= j_ < lst.len() && is_odd(lst[j_]) && is_first_odd(j_, lst) &&
                                   prod_i64 as int == lst[i_] * lst[j_];
    }
    let product = prod_i64 as i32;
    product
}
// </vc-code>

fn main() {
}

}