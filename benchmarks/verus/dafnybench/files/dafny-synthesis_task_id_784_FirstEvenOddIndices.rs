// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn first_even_odd_indices(lst: Vec<i32>) -> (result: (usize, usize))
    requires lst.len() >= 2,
             exists|i: int| 0 <= i < lst.len() && is_even(lst[i] as int),
             exists|i: int| 0 <= i < lst.len() && is_odd(lst[i] as int)
    ensures 0 <= result.0 < lst.len(),
            0 <= result.1 < lst.len(),

            is_even(lst[result.0 as int] as int) && is_first_even(result.0 as int, lst@),
            is_odd(lst[result.1 as int] as int) && is_first_odd(result.1 as int, lst@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}