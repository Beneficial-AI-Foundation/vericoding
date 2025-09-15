// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed as it's not needed with the new iteration logic. */
// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `Map` struct in Verus does not have a `get_or_else` method directly. Instead, `get` returns an `Option`, and you can handle the `None` case manually. The `dom()` method returns a `Set<K>`, which is not directly iterable with a `for...in` loop. The alternative is to convert the map to a `Vec` for sorting, which has been done by explicitly creating a `Vec` and pushing elements into it. The issue regarding iterating the `dom()` was fixed by using `counts.keys()` which returns an iterable type. Also included an explicit assertion to satisfy the verifier when calling `unwrap()` */
{
    let mut counts: Map<i32, nat> = Map::empty();
    for x in nums.iter() {
        let current_count = counts.get(*x).unwrap_or(0);
        counts = counts.insert(*x, current_count + 1);
    }

    let mut freq_vec: Vec<(i32, nat)> = Vec::new();
    // Convert map to a vector of (key, value) pairs for sorting.
    for x in counts.keys() {
        proof {
            assert(counts.dom().contains(*x));
        }
        freq_vec.push((*x, counts.get(*x).unwrap()));
    }

    freq_vec.sort_by(|a, b| b.1.cmp(&a.1));

    let mut result: Vec<i32> = Vec::new();

    for i in 0..k {
        if i < freq_vec.len() {
            result.push(freq_vec[i].0);
        }
    }
    result
}
// </vc-code>

}
fn main() {}