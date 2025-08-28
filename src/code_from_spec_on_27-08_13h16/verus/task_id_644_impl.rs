use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is fixed in the code section syntax
// </vc-helpers>

// <vc-spec>
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    // pre-conditions-start
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n && n <= list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut result = Vec::new();
    let mut i: usize = 0;

    // Reverse the first n elements
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall |k: int| 0 <= k < i ==> result@[k] == list@[(n as int - 1 - k)],
    {
        result.push(list@[(n - 1 - i) as int]);
        i = i + 1;
    }

    // Copy the remaining elements
    let mut j: usize = n;
    while j < list@.len()
        invariant
            n <= j <= list@.len(),
            result@.len() == j,
            forall |k: int| 0 <= k < n ==> result@[k] == list@[(n as int - 1 - k)],
            forall |k: int| n <= k < j ==> result@[k] == list@[k],
    {
        result.push(list@[j]);
        j = j + 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() {}