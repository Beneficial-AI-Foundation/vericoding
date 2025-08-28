use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
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
{
    let mut reversed_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            n < list@.len(),
            reversed_list@.len() == i,
            forall |k: usize| 0 <= k < i ==> reversed_list@[k] == list@[(i - 1 - k) as int],
        decreases n - i
    {
        reversed_list.push(list[i]);
        i = i + 1;
    }
    
    let mut j: usize = n;
    while j < list.len()
        invariant
            n <= j <= list@.len(),
            reversed_list@.len() == j,
            forall |k: usize| 0 <= k < n ==> reversed_list@[k] == list@[(n - 1 - k) as int],
            forall |k: usize| n <= k < j ==> reversed_list@[k] == list@[k as int],
        decreases list@.len() - j
    {
        reversed_list.push(list[j]);
        j = j + 1;
    }
    
    reversed_list
}
// </vc-code>

} // verus!

fn main() {}