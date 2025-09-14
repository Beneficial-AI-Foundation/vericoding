// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Added decreases clause to the while loop to ensure termination verification. */
    let len = list.len();
    let mut result = Vec::with_capacity(len);
    let mut i = n;
    while i > 0
        decreases i
    {
        i -= 1;
        result.push(list[i]);
    }
    for i in n..len {
        result.push(list[i]);
    }
    result
}
// </vc-code>

}
fn main() {}