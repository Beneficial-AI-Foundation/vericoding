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
    requires exists|i: int| 0 <= i < lst.len(), #[trigger] is_even(lst[i]),
    requires exists|i: int| 0 <= i < lst.len(), #[trigger] is_odd(lst[i]),
    ensures ({
        let (even_index, odd_index) = r;
        &&& 0 <= even_index < lst.len()
        &&& 0 <= odd_index < lst.len()
        &&& is_even(lst[even_index as int]) && is_first_even(even_index as int, lst)
        &&& is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst)
    }),
{
    let mut even_idx: usize = 0;
    let mut odd_idx: usize = 0;
    let mut found_even: bool = false;
    let mut found_odd: bool = false;

    // Find the first even number
    #[invariant_loop
        0 <= even_idx,
        even_idx <= lst.len(),
        !found_even ==> (forall|i: int| 0 <= i < even_idx as int ==> is_odd(lst[i])),
        found_even ==> (0 <= even_idx as int && even_idx as int < lst.len() && is_even(lst[even_idx as int]) && is_first_even(even_idx as int, lst)),
        // The existence of an even number in the list
        exists|k: int| 0 <= k < lst.len() && is_even(lst[k]),
    ]
    while even_idx < lst.len() && !found_even
    {
        if is_even(lst[even_idx as int]) {
            found_even = true;
        } else {
            even_idx = even_idx + 1;
        }
    }
    
    proof {
        assert(found_even) by {
            assert(exists|i:int| 0 <= i < lst.len() && is_even(lst[i])); // from precondition
            
            // Prove that found_even must be true, otherwise a contradiction arises.
            // If !found_even and the loop terminated, it means even_idx reached lst.len().
            // And from the invariant: !found_even ==> (forall|i: int| 0 <= i < even_idx as int ==> is_odd(lst[i])).
            // This would imply that all elements in lst (from 0 to lst.len() - 1) are odd,
            // which contradicts the precondition that an even number exists.
            if !found_even {
                assert(even_idx == lst.len());
                assert(forall|i: int| 0 <= i < even_idx as int ==> is_odd(lst[i]));
                assert(forall|i: int| 0 <= i < lst.len() ==> is_odd(lst[i]));
                assert(false); // Contradiction with exists even
            }
        }
        assert(even_idx as int < lst.len()); // derived from found_even and invariant
    }


    // Find the first odd number
    #[invariant_loop
        0 <= odd_idx,
        odd_idx <= lst.len(),
        !found_odd ==> (forall|i: int| 0 <= i < odd_idx as int ==> is_even(lst[i])),
        found_odd ==> (0 <= odd_idx as int && odd_idx as int < lst.len() && is_odd(lst[odd_idx as int]) && is_first_odd(odd_idx as int, lst)),
        // The existence of an odd number in the list
        exists|k: int| 0 <= k < lst.len() && is_odd(lst[k]),
    ]
    while odd_idx < lst.len() && !found_odd
    {
        if is_odd(lst[odd_idx as int]) {
            found_odd = true;
        } else {
            odd_idx = odd_idx + 1;
        }
    }

    proof {
        assert(found_odd) by {
            assert(exists|i:int| 0 <= i < lst.len() && is_odd(lst[i])); // from precondition

            // Similar proof for found_odd as for found_even
            if !found_odd {
                assert(odd_idx == lst.len());
                assert(forall|i: int| 0 <= i < odd_idx as int ==> is_even(lst[i]));
                assert(forall|i: int| 0 <= i < lst.len() ==> is_even(lst[i]));
                assert(false); // Contradiction with exists odd
            }
        }
        assert(odd_idx as int < lst.len()); // derived from found_odd and invariant
    }

    (even_idx, odd_idx)
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
    let even_val = lst[even_index as int];
    let odd_val = lst[odd_index as int];

    (even_val * odd_val) as i32
}
// </vc-code>

fn main() {
}

}