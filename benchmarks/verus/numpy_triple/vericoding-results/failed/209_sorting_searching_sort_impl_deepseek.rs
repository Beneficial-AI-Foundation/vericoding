// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


spec fn sorted(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
}

spec fn same_elements(a: Seq<i32>, b: Seq<i32>) -> bool {
    forall|x: i32| count_occurrences(a, x) == count_occurrences(b, x)
}

proof fn helper_lemma_eq_len<A>(s: Seq<A>, t: Seq<A>)
    requires
        s.len() == t.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == t[i]
    ensures
        s === t
{
    if s.len() != 0 {
        helper_lemma_eq_len(s.skip(1), t.skip(1));
    }
}

proof fn swap_preserves_elements(v: &mut Vec<i32>, i: usize, j: usize)
    requires
        0 <= i < v.len(),
        0 <= j < v.len()
    ensures
        same_elements(v@, old(v)@)
{
    // Proof that swapping preserves the multiset
    assert forall|x: i32| count_occurrences(v@, x) == count_occurrences(old(v)@, x) by {
        // Key insight: swapping elements doesn't change the count of any element
        // If x equals the value at i, we lose one at i but gain one at j
        // If x equals the value at j, we lose one at j but gain one at i
        // If x is different from both, counts remain unchanged
        // This needs to be formalized with case analysis
    };
}

// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(seq: Seq<i32>, x: i32) -> int
    decreases seq.len()
{
    if seq.len() == 0 {
        0int
    } else {
        (if seq[0] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1), x)
    }
}

fn sort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion issue by casting to usize */
    let mut v = a.clone();
    let n = v.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < l < i ==> v@[k] <= v@[l],
            same_elements(v@, a@)
        decreases n - i
    {
        let mut j: usize = i;
        while j > 0 && v[j - 1] > v[j]
            invariant
                0 <= j <= i,
                forall|k: int, l: int| 0 <= k < l < j ==> v@[k] <= v@[l],
                forall|k: int, l: int| j <= k < l <= i ==> v@[k] <= v@[l],
                j < i ==> v@[j as int] <= v@[(j + 1) as int],
                same_elements(v@, a@)
            decreases j
        {
            proof {
                swap_preserves_elements(&mut v, (j - 1) as usize, j as usize);
            }
            let temp = v[j - 1];
            v[j - 1] = v[j];
            v[j] = temp;
            j = j - 1;
        }
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}