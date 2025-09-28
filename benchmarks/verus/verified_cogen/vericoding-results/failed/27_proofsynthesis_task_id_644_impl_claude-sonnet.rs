// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified swap function with correct specification */
fn swap_elements(list: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < old(list)@.len(),
        j < old(list)@.len(),
    ensures
        list@.len() == old(list)@.len(),
        list@[i as int] == old(list)@[j as int],
        list@[j as int] == old(list)@[i as int],
        forall|k: int| 0 <= k < list@.len() && k != i as int && k != j as int ==> list@[k] == old(list)@[k],
{
    let temp = list[i];
    let val_j = list[j];
    list.set(i, val_j);
    list.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)

    requires
        list@.len() > 0,
        0 < n < list@.len(),

    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants and swapping logic */
    let mut result = list.clone();
    let mut i: usize = 0;
    let mut j: usize = n - 1;
    
    while i < j
        invariant
            result@.len() == list@.len(),
            0 <= i <= n,
            j < n,
            i <= j + 1,
            forall|k: int| n <= k < result@.len() ==> result@[k] == list@[k],
            forall|k: int| i <= k <= j ==> result@[k] == list@[k],
            forall|k: int| 0 <= k < i ==> result@[k] == list@[j as int + 1 + k],
            forall|k: int| j < k < n ==> result@[k] == list@[n as int - 1 - k + j as int + 1],
        decreases j - i,
    {
        swap_elements(&mut result, i, j);
        i = i + 1;
        j = j - 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}