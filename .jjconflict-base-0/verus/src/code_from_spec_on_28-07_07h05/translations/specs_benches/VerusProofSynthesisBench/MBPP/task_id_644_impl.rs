use vstd::prelude::*;

verus! {

//IMPL reverse_to_k
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
{
    let mut result = Vec::new();
    
    // Add the first n elements in reverse order
    let mut i = n;
    /* code modified by LLM (iteration 3): fixed loop invariant and bounds checking */
    while i > 0
        invariant
            i <= n,
            result@.len() == n - i,
            result@ == list@.subrange(i as int, n as int).reverse(),
            i <= list.len(), // ensure i is within bounds
        decreases i,
    {
        i = i - 1;
        /* code modified by LLM (iteration 3): add bounds check assertion */
        assert(i < list.len()); // i went from > 0 to >= 0, and n < list.len()
        result.push(list[i]);
    }
    
    // Add the remaining elements in original order
    let mut j = n;
    /* code modified by LLM (iteration 3): added bounds assertion */
    while j < list.len()
        invariant
            n <= j <= list.len(),
            result@.len() == n + (j - n),
            result@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, j as int)
            ),
        decreases list.len() - j,
    {
        /* code modified by LLM (iteration 3): add bounds check assertion */
        assert(j < list.len());
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}

} // verus!

fn main() {}