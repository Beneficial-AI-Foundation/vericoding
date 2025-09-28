// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove sortedness between two indices */
proof fn lemma_sorted_prefix(s: Vec<i8>, a: int, b: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
        0 <= a < b < s@.len(),
    ensures
        s@[a] <= s@[b],
    decreases
        s@.len(),
{
    // Directly use the global sortedness hypothesis
    assert(forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j]);
    assert(0 <= a && a < b && b < s@.len());
    assert(s@[a] <= s@[b]);
}

// </vc-helpers>

// <vc-spec>
fn unique_sorted(s: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
    ensures 
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> s@.contains(x),
        forall|x: i8| s@.contains(x) ==> result@.contains(x),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): construct unique sorted vector by skipping duplicates */
{
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    let n: usize = s.len();

    while i < n
        invariant
            0 <= i as int <= s@.len(),
            forall|x: i8| res@.contains(x) ==> (exists|k: int| 0 <= k < i as int && s@[k] == x),
            forall|k: int| 0 <= k < i as int ==> res@.contains(s@[k]),
            forall|p: int, q: int| 0 <= p < q < res@.len() ==> res@[p] < res@[q],
        decreases s@.len() - i as int
    {
        let cur: i8 = s[i];
        if res.len() == 0 || cur > res[res.len() - 1] {
            res.push(cur);
        } else {
            let last: i8 = res[res.len() - 1];
            proof {
                // From the else branch we have res.len() != 0 and cur <= last
                assert(!(res.len() == 0 || cur > res[res.len() - 1]));
                assert(cur <= last);
                // last was produced from some earlier position in s
                assert(res@.contains(last));
                let k: int = choose|k: int| 0 <= k < i as int && s@[k] == last;
                lemma_sorted_prefix(s, k, i as int);
                // lemma gives s@[k] <= s@[i]
                assert(s@[k] <= s@[i as int]);
                assert(last <= cur);
                // combine cur <= last and last <= cur to conclude equality
                assert(cur == last);
            }
        }
        i = i + 1;
    }

    res
}

// </vc-code>


}

fn main() {}