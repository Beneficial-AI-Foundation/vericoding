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
proof fn lemma_first_even_unique(lst: Seq<int>, i1: int, i2: int)
    requires 0 <= i1 < lst.len() && is_even(lst[i1]) && is_first_even(i1, lst),
    requires 0 <= i2 < lst.len() && is_even(lst[i2]) && is_first_even(i2, lst),
    ensures i1 == i2,
{
    if i1 != i2 {
        if i1 < i2 {
            assert(is_odd(lst[i2]));
            assert(is_even(lst[i2]));
            assert(false);
        } else {
            assert(is_odd(lst[i1]));
            assert(is_even(lst[i1]));
            assert(false);
        }
    }
}

proof fn lemma_first_odd_unique(lst: Seq<int>, i1: int, i2: int)
    requires 0 <= i1 < lst.len() && is_odd(lst[i1]) && is_first_odd(i1, lst),
    requires 0 <= i2 < lst.len() && is_odd(lst[i2]) && is_first_odd(i2, lst),
    ensures i1 == i2,
{
    if i1 != i2 {
        if i1 < i2 {
            assert(is_even(lst[i2]));
            assert(is_odd(lst[i2]));
            assert(false);
        } else {
            assert(is_even(lst[i1]));
            assert(is_odd(lst[i1]));
            assert(false);
        }
    }
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
    let mut even_index: usize = 0;
    let mut odd_index: usize = 0;
    let mut found_even = false;
    let mut found_odd = false;
    
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            found_even ==> (0 <= even_index < lst.len() && is_even(lst[even_index as int]) && is_first_even(even_index as int, lst)),
            found_odd ==> (0 <= odd_index < lst.len() && is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst)),
            !found_even ==> forall|j: int| 0 <= j < i ==> is_odd(lst[j]),
            !found_odd ==> forall|j: int| 0 <= j < i ==> is_even(lst[j]),
    {
        if !found_even && is_even(lst[i as int]) {
            even_index = i;
            found_even = true;
        }
        if !found_odd && is_odd(lst[i as int]) {
            odd_index = i;
            found_odd = true;
        }
        i += 1;
    }
    
    let product = (lst[even_index as int] * lst[odd_index as int]) as i32;
    
    proof {
        assert(found_even);
        assert(found_odd);
        assert(0 <= even_index < lst.len());
        assert(0 <= odd_index < lst.len());
        assert(is_even(lst[even_index as int]) && is_first_even(even_index as int, lst));
        assert(is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst));
        assert(product as int == lst[even_index as int] * lst[odd_index as int]);
    }
    
    product
}
// </vc-code>

fn main() {
}

}