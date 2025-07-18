use vstd::prelude::*;

verus! {

//IMPL reverse_to_k
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        list.len() > 0,
        0 < n < list.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fixed function structure by moving requires/ensures before body and implementing proper return value */
    let mut result = Vec::new();
    
    // Add the first n elements in reverse order
    let mut i = n;
    while i > 0
        invariant
            i <= n,
            result@.len() == n - i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == list@[n as int - 1 - j],
    {
        i = i - 1;
        result.push(list[i]);
    }
    
    // Add the remaining elements
    let mut j = n;
    while j < list.len()
        invariant
            n <= j <= list.len(),
            result@.len() == n + (j - n),
            forall|k: int| 0 <= k < n ==> result@[k] == list@[n as int - 1 - k],
            forall|k: int| n <= k < result@.len() ==> result@[k] == list@[n as int + (k as int - n as int)],
    {
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}

} // verus!

fn main() {}