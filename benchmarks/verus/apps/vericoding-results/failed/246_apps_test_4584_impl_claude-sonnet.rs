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
/* helper modified by LLM (iteration 5): Fixed invariant and overflow handling with proper bounds */
fn count_subordinates(aa: &Vec<i8>, boss_id: i8) -> (count: i8)
    requires aa@.len() < 128
    ensures count as int == subordinate_count(aa@.map(|i, x| x as int), boss_id as int)
{
    let mut count = 0i8;
    let mut j = 0;
    
    while j < aa.len()
        invariant
            0 <= j <= aa.len(),
            count as int == Set::new(|idx: int| 0 <= idx < j as int && aa@[idx] as int == boss_id as int).len() as int,
            count >= 0,
            count <= aa.len(),
        decreases aa.len() - j
    {
        if aa[j] == boss_id {
            count = count + 1;
        }
        j = j + 1;
    }
    
    proof {
        assert(Set::new(|idx: int| 0 <= idx < aa.len() && aa@[idx] as int == boss_id as int) =~= Set::new(|idx: int| 0 <= idx < j as int && aa@[idx] as int == boss_id as int));
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, aa: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, aa@.map(|i, x| x as int))
    ensures valid_output(n as int, aa@.map(|i, x| x as int), result@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added length constraint checking */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] as int == subordinate_count(aa@.map(|i, x| x as int), k + 1),
            aa@.len() < 128,
        decreases n - i
    {
        let count = count_subordinates(&aa, (i + 1) as i8);
        result.push(count);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}