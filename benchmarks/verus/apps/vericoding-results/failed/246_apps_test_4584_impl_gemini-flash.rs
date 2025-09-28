// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, aa: Seq<int>) -> bool {
    n >= 2 &&
    aa.len() == n - 1 &&
    forall|i: int| 0 <= i < aa.len() ==> #[trigger] aa[i] >= 1 && #[trigger] aa[i] < i + 2
}

spec fn subordinate_count(aa: Seq<int>, boss_id: int) -> int {
    Set::new(|j: int| 0 <= j < aa.len() && aa[j] == boss_id).len() as int
}

spec fn valid_output(n: int, aa: Seq<int>, result: Seq<int>) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> #[trigger] result[i] >= 0 &&
    forall|i: int| 0 <= i < n ==> #[trigger] result[i] == subordinate_count(aa, i + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, aa: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, aa@.map(|i, x| x as int))
    ensures valid_output(n as int, aa@.map(|i, x| x as int), result@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The `subordinate_count` within the while loop invariant was pointing to a sub-sequence `aa_ghost.subsequence(0, j as int)`, this `subsequence` needs to be `aa_ghost`. I also removed `boss_id` as `i8` as `int` cast and `result@[k_idx as nat] as int` cast for `subordinate_count` to avoid overflow. And the `(j as int) < aa_ghost.len()` invariant condition to `j < aa_ghost.len()` as no conversion of `j` is needed as the index into `aa_ghost` will match `j` as usize. */
    let mut result: Vec<i8> = Vec::new();
    let n_usize = n as usize;

    // Initialize result with zeros
    let mut i: usize = 0;
    while i < n_usize
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j as nat] == 0
        decreases n_usize - i
    {
        result.push(0);
        i = i + 1;
    }

    // Populate subordinate counts
    let mut j: usize = 0;
    let aa_ghost = aa@.map(|idx, x| x as int);
    while j < n_usize - 1
        invariant
            0 <= j as int <= n as int - 1,
            j < aa_ghost.len(),
            result.len() == n_usize,
            forall|k_idx: int| 0 <= k_idx < n as int ==> result@[k_idx as nat] == subordinate_count(aa_ghost, k_idx + 1),
            forall|k_idx: int| 0 <= k_idx < n as int ==> result@[k_idx as nat] >= 0
        decreases (n_usize - 1) - j
    {
        let boss_id: i8 = aa[j];
        let boss_idx: usize = (boss_id - 1) as usize;

        result.set(boss_idx, result[boss_idx] + 1);
        j = j + 1;
    }
    result
}
// </vc-code>


}

fn main() {}