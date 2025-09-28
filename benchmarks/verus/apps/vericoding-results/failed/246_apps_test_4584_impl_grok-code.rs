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
    /* code modified by LLM (iteration 5): Fixed compilation error by changing runtime types from int to usize for boss, count, and i variables */
    let mut result: Vec<i8> = Vec::with_capacity(n as usize);
    let mut boss: usize = 1;
    while boss <= n as usize
        invariant
            result@.len() as int == boss as int - 1,
            forall|k: int|(0 <= k < boss as int - 1 && boss as int - 1 <= n as int) ==> result@[k] == subordinate_count(aa@.map(|ii, x| x as int), k + 1),
            aa@.len() == n as int - 1,
        decreases n as nat - boss as nat
    {
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < aa.len()
            invariant
                count as int == Set::new(|j: int| 0 <= j < i as int && aa@[j] == boss as int).len(),
                i <= aa@.len() as nat,
                boss as int <= n as int,
            decreases aa@.len() as nat - i as nat
        {
            if (aa[i] as usize) == boss {
                count = count + 1;
            }
            i = i + 1;
        }
        proof {
            assert(count as int == subordinate_count(aa@.map(|ii, x| x as int), boss as int));
        }
        result.push(count as i8);
        boss = boss + 1;
    }
    proof {
        assert(result@.len() as int == n as int);
        assert(forall|i: int| 0 <= i < n as int ==> result@[i] == subordinate_count(aa@.map(|ii, x| x as int), i + 1));
    }
    result
}
// </vc-code>


}

fn main() {}