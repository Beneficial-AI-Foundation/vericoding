// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed parameter type from int to nat for compatibility */
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn swap_invariant(s: Seq<i32>, original: Seq<i32>) -> bool {
    s.len() == original.len() && s.to_multiset() == original.to_multiset()
}

spec fn bubble_partial_sorted(s: Seq<i32>, up_to: int) -> bool {
    forall|k: int, l: int| 0 <= k < l < up_to ==> s[k] <= s[l]
}

spec fn largest_elements_at_end(s: Seq<i32>, sorted_suffix: nat) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() - sorted_suffix && s.len() - sorted_suffix <= j < s.len() ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotation to fix quantifier inference */
    let mut result = a.clone();
    let n = result.len();
    
    if n <= 1 {
        return result;
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == n,
            n == a.len(),
            swap_invariant(result@, a@),
            largest_elements_at_end(result@, i as nat),
        decreases n - i
    {
        let mut j = 0;
        while j < n - 1 - i
            invariant
                0 <= j <= n - 1 - i,
                0 <= i < n,
                result.len() == n,
                swap_invariant(result@, a@),
                largest_elements_at_end(result@, i as nat),
                forall|k: int| 0 <= k < j ==> #[trigger] result[k] <= #[trigger] result[k + 1],
            decreases n - 1 - i - j
        {
            if result[j] > result[j + 1] {
                let temp = result[j];
                result.set(j, result[j + 1]);
                result.set(j + 1, temp);
            }
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}