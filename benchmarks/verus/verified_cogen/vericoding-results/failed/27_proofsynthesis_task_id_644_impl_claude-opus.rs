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
    /* code modified by LLM (iteration 5): fixed type comparison error */
    let mut result = Vec::new();
    
    // Add reversed portion (0 to n)
    let mut i: usize = n;
    while i > 0
        invariant
            i <= n,
            result@.len() == (n - i) as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == list@[(n - 1 - j) as int],
            result@ == list@.subrange((n - i) as int, n as int).reverse(),
        decreases i
    {
        i = i - 1;
        result.push(list[i]);
        proof {
            assert(list@.subrange((n - i - 1) as int, n as int).reverse().len() == i + 1);
            let new_seq = list@.subrange((n - i - 1) as int, n as int).reverse();
            assert(new_seq[0] == list@[(n - 1) as int]);
            if i as int < (n - 1) as int {
                assert(forall|k: int| 1 <= k < new_seq.len() ==> new_seq[k] == list@[(n - 1 - k) as int]);
            }
        }
    }
    
    proof {
        assert(i == 0);
        assert(result@.len() == n as int);
        assert(result@ == list@.subrange(0, n as int).reverse());
    }
    
    // Add remaining portion (n to end)
    let mut j: usize = n;
    while j < list.len()
        invariant
            n <= j <= list.len(),
            result@.len() == n + (j - n) as int,
            result@.subrange(0, n as int) == list@.subrange(0, n as int).reverse(),
            result@.subrange(n as int, result@.len() as int) == list@.subrange(n as int, j as int),
            result@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, j as int)),
        decreases list.len() - j
    {
        result.push(list[j]);
        j = j + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}