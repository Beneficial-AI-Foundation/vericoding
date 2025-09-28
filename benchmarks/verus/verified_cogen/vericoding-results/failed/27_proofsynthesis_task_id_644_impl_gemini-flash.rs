// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a stub for helper function */

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
/* code modified by LLM (iteration 5): Fixed `nat` casting */
{
    let mut new_list = Vec::new();
    let mut i: usize = n - 1;
    while (i < n && i >= 0)
        invariant
            0 <= i as int <= n as int - 1,
            new_list@.len() as int == (n as int - (i as int + 1)),
            new_list@ == list@.subrange(0, n as int).subrange(i as int + 1, n as int).reverse(),
        decreases i
    {
        new_list.push(list[i]);
        i = i - 1;
    }
    let mut j: usize = n;
    while (j < list@.len() as usize)
        invariant
            n as int <= j as int <= list@.len() as int,
            new_list@.len() as int == n as int + (j as int - n as int),
            new_list@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, j as int),
            ),
        decreases list@.len() as int - j as int
    {
        new_list.push(list[j]);
        j = j + 1;
    }
    new_list
}
// </vc-code>

}
fn main() {}