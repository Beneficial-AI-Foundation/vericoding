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
    let mut reversed_list = Vec::new();
    let mut i: usize = n;
    while i > 0
        invariant
            0 <= i <= n,
            reversed_list@ == list@.subrange(i as int, n as int).reverse(),
        decreases i
    {
        i = i - 1;
        reversed_list.push(list[i]);
    }

    let mut j: usize = n;
    while j < list.len()
        invariant
            n <= j <= list.len(),
            reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, j as int)),
        decreases list.len() - j
    {
        reversed_list.push(list[j]);
        j = j + 1;
    }

    reversed_list
}
// </vc-code>

}
fn main() {}