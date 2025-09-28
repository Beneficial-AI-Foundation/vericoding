// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn reverse_sublist_preserves_tail(list: Seq<i32>, n: int)
    requires
        0 < n < list.len(),
    ensures
        list.subrange(0, n).reverse().add(list.subrange(n, list.len())) == list,
{
    // Use built-in sequence lemmas to prove the equality
    assert(list.subrange(0, n).reverse().add(list.subrange(n, list.len())) =~= list);
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
    /* code modified by LLM (iteration 5): Fix int/nat casting and ghost code usage */
    let mut reversed_list = Vec::new();
    
    // Build the first n elements in reverse order
    let mut i: usize = n;
    ghost {
        proof {
            reverse_sublist_preserves_tail(list@, n as int);
        }
    }
    while i > 0
        invariant
            i <= n,
            reversed_list@ == list@.subrange(i as int, n as int).reverse(),
    {
        i -= 1;
        reversed_list.push(list[i]);
    }
    
    // Add the remaining elements unchanged
    let mut j: usize = n;
    while j < list.len()
        invariant
            j >= n,
            j <= list.len(),
            reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, j as int)),
    {
        reversed_list.push(list[j]);
        j += 1;
    }
    
    reversed_list
}
// </vc-code>

}
fn main() {}