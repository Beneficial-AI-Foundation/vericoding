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
    /* code modified by LLM (iteration 4): Fixed overflow issues and invariants */
    let mut result: Vec<i8> = Vec::new();
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            i <= 127,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] >= 0,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == subordinate_count(aa@.map(|k, x| x as int), j + 1),
        decreases n - i
    {
        let mut count: i8 = 0;
        let mut j: usize = 0;
        assert(i < n);
        assert(i + 1 <= n);
        assert(i + 1 <= 127);
        while j < aa.len()
            invariant
                0 <= j <= aa.len(),
                0 <= count,
                count <= aa.len(),
                count as int == Set::new(|k: int| 0 <= k < j && aa@[k] == (i + 1) as int).len(),
            decreases aa.len() - j
        {
            if aa[j] == (i + 1) {
                assert(count < aa.len());
                count = count + 1;
            }
            j = j + 1;
        }
        assert(count as int == subordinate_count(aa@.map(|k, x| x as int), (i + 1) as int));
        result.push(count);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}