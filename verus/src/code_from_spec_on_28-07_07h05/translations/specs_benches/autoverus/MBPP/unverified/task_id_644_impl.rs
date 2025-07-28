use vstd::prelude::*;
fn main() {}

verus! {

//IMPL reverse_to_k
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
    /* code modified by LLM (iteration 3): added trigger annotations to fix quantifier trigger inference */
    while i > 0
        invariant
            i <= n,
            n < list@.len(),
            result@.len() == (n - i) as int,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] == list@[n as int - 1 - j] && {
                let idx = n as int - 1 - j;
                0 <= idx < list@.len()
            },
        decreases i,
    {
        i = i - 1;
        /* code modified by LLM (iteration 2): added assertion to help prove bounds */
        assert(i < n);
        assert(i < list.len());
        result.push(list[i]);
    }
    
    // Add the remaining elements in original order
    let mut j = n;
    /* code modified by LLM (iteration 3): added trigger annotations to fix quantifier trigger inference */
    while j < list.len()
        invariant
            n <= j <= list.len(),
            n < list@.len(),
            result@.len() == (n + (j - n)) as int,
            forall|k: int| 0 <= k < n as int ==> #[trigger] result@[k] == list@[n as int - 1 - k] && {
                let idx = n as int - 1 - k;
                0 <= idx < list@.len()
            },
            forall|k: int| n as int <= k < result@.len() ==> #[trigger] result@[k] == list@[k],
        decreases list.len() - j,
    {
        /* code modified by LLM (iteration 2): added assertion to help prove bounds */
        assert(j < list.len());
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}

} // verus!