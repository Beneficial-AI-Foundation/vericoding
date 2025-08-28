use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let mut result = Vec::new();
    
    // First, add the reversed portion from 0 to n
    let mut i = n;
    while i > 0
        invariant
            i <= n,
            result.len() == n - i,
            forall|j: int| 0 <= j < result.len() ==> result@[j] == list@[(n - 1 - j) as int],
        decreases i
    {
        i = i - 1;
        result.push(list[i]);
    }
    
    // Then, add the remaining portion from n to end
    let mut j = n;
    while j < list.len()
        invariant
            n <= j <= list.len(),
            result.len() == n + (j - n),
            forall|k: int| 0 <= k < n ==> result@[k] == list@[(n - 1 - k) as int],
            forall|k: int| n <= k < result.len() ==> result@[k] == list@[n + (k - n)],
        decreases list.len() - j
    {
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}