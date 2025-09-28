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
/* helper modified by LLM (iteration 5): trivial lemma proving 0 equals 0 to avoid quantifier trigger issues */
fn lemma_zero()
    ensures
        0_i8 == 0_i8,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, aa: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, aa@.map(|i, x| x as int))
    ensures valid_output(n as int, aa@.map(|i, x| x as int), result@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): initialize counts with zeros and count subordinates */
    let un: usize = n as usize;
    let mut counts: Vec<i8> = Vec::new();
    let mut j: usize = 0;
    while j < un
        invariant
            j <= un,
            counts.len() == j,
        decreases un - j
    {
        counts.push(0_i8);
        j += 1;
    }

    let mut i: usize = 0;
    while i < aa.len()
        invariant
            i <= aa.len(),
            counts.len() == un,
        decreases aa.len() - i
    {
        let boss_i8: i8 = aa[i];
        let pos: usize = (boss_i8 - 1_i8) as usize;
        counts[pos] = counts[pos] + 1_i8;
        i += 1;
    }
    counts
}
// </vc-code>


}

fn main() {}