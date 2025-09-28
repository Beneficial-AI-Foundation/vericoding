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
proof fn lemma_even_index_exists(lst: Seq<int>)
    requires
        lst.len() >= 2,
        exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
    ensures
        exists|i: int| 0 <= i < lst.len() && is_even(lst[i]) && is_first_even(i, lst),
{
    let mut index: int = 0;
    
    while index < lst.len()
        invariant
            0 <= index <= lst.len(),
            exists|i: int| index <= i < lst.len() && is_even(lst[i]),
            forall|j: int| 0 <= j < index ==> is_odd(lst[j]),
    {
        if is_even(lst[index]) {
            assert(forall|j: int| 0 <= j < index ==> is_odd(lst[j]));
            assert(is_first_even(index, lst));
            return;
        } else {
            assert(is_odd(lst[index]));
            index = index + 1;
            if index < lst.len() {
                assert(exists|i: int| index <= i < lst.len() && is_even(lst[i]));
            }
        }
    }
}

proof fn lemma_odd_index_exists(lst: Seq<int>)
    requires
        lst.len() >= 2,
        exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]),
    ensures
        exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]) && is_first_odd(i, lst),
{
    let mut index: int = 0;
    
    while index < lst.len()
        invariant
            0 <= index <= lst.len(),
            exists|i: int| index <= i < lst.len() && is_odd(lst[i]),
            forall|j: int| 0 <= j < index ==> is_even(lst[j]),
    {
        if is_odd(lst[index]) {
            assert(forall|j: int| 0 <= j < index ==> is_even(lst[j]));
            assert(is_first_odd(index, lst));
            return;
        } else {
            assert(is_even(lst[index]));
            index = index + 1;
            if index < lst.len() {
                assert(exists|i: int| index <= i < lst.len() && is_odd(lst[i]));
            }
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
    let (even_index, odd_index) = first_even_odd_indices(lst);
    proof {
        lemma_even_index_exists(lst);
        lemma_odd_index_exists(lst);
    }
    assert(is_even(lst[even_index as int]) && is_first_even(even_index as int, lst));
    assert(is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst));
    (lst[even_index as int] * lst[odd_index as int]) as i32
}
// </vc-code>

fn main() {
}

}