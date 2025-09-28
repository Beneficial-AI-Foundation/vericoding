// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)

    requires
        list@.len() > 0,
        0 < n < list@.len(),

    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to both loops */
    let mut result = Vec::new();
    
    // Add elements from index n to end
    let mut i = n;
    while i < list.len()
        invariant
            n <= i <= list.len(),
            result@ == list@.subrange(n as int, i as int)
        decreases list.len() - i
    {
        result.push(list[i]);
        i = i + 1;
    }
    
    // Add elements from index 0 to n
    let mut j = 0;
    while j < n
        invariant
            0 <= j <= n,
            n <= list.len(),
            result@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, j as int))
        decreases n - j
    {
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}