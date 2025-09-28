use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

spec fn is_first_even(even_index: int, lst: Seq<i32>) -> bool
    recommends 0 <= even_index < lst.len(), is_even(lst[even_index] as int)
{
    forall|i: int| 0 <= i < even_index ==> is_odd(lst[i] as int)
}

spec fn is_first_odd(odd_index: int, lst: Seq<i32>) -> bool
    recommends 0 <= odd_index < lst.len(), is_odd(lst[odd_index] as int)
{
    forall|i: int| 0 <= i < odd_index ==> is_even(lst[i] as int)
}

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn first_even_odd_indices(lst: Vec<i32>) -> (result: (usize, usize))
    requires lst.len() >= 2,
             exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int),
             exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int)
    ensures 0 <= result.0 < lst.len(),
            0 <= result.1 < lst.len(),
            // This is the postcondition that ensures that it's the first, not just any
            is_even(lst[result.0 as int] as int) && is_first_even(result.0 as int, lst@),
            is_odd(lst[result.1 as int] as int) && is_first_odd(result.1 as int, lst@)
// </vc-spec>
// <vc-code>
{
    let mut even_index: usize = 0;
    while even_index < lst.len() && !(lst[even_index] % 2 == 0)
        invariant
            0 <= even_index <= lst.len()@,
            forall|k: int| 0 <= k < (even_index as int) ==> #[trigger] is_odd(lst@[k] as int),
            exists|k: int| (even_index as int) <= k && k < lst@.len() && #[trigger] is_even(lst@[k] as int)
        decreases lst.len() - even_index
    {
        even_index += 1;
    }
    assert(even_index < lst.len()); // ensures we found it

    let mut odd_index: usize = 0;
    while odd_index < lst.len() && !(lst[odd_index] % 2 != 0)
        invariant
            0 <= odd_index <= lst.len()@,
            forall|k: int| 0 <= k < (odd_index as int) ==> #[trigger] is_even(lst@[k] as int),
            exists|k: int| (odd_index as int) <= k && k < lst@.len() && #[trigger] is_odd(lst@[k] as int)
        decreases lst.len() - odd_index
    {
        odd_index += 1;
    }
    assert(odd_index < lst.len()); // ensures we found it

    (even_index, odd_index)
}
// </vc-code>

fn main() {}

}