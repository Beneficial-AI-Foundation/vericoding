use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut result = Vec::new();
    
    // Add the first n elements in reverse order
    let mut i = n;
    /* code modified by LLM (iteration 2): fixed invariant and added bounds check */
    while i > 0
        invariant
            i <= n,
            n < list@.len(),
            result@.len() == (n - i) as int,
            result@ == list@.subrange(i as int, n as int).reverse(),
        decreases i,
    {
        i = i - 1;
        /* code modified by LLM (iteration 2): added assertion to help verification */
        assert(i < n);
        assert(n < list@.len());
        assert(i < list@.len());
        result.push(list[i]);
    }
    
    // Add the remaining elements
    let mut j = n;
    /* code modified by LLM (iteration 2): updated invariant to match postcondition */
    while j < list.len()
        invariant
            n <= j <= list.len(),
            result@.len() == (n + (j - n)) as int,
            result@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, j as int)
            ),
        decreases list.len() - j,
    {
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}

} // verus!