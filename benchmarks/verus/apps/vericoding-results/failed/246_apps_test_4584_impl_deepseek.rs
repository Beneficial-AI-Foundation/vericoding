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

proof fn lemma_sequence_map_properties(n: int, aa: Seq<int>) 
    requires valid_input(n, aa)
    ensures forall|i: int| 0 <= i < aa.len() ==> aa[i] >= 1 && aa[i] <= n - 1
{
    assert forall|i: int| 0 <= i < aa.len() implies aa[i] >= 1 && aa[i] <= n - 1 by {
        assert(valid_input(n, aa));
        assert(valid_input(n, aa) ==> (forall|i: int| 0 <= i < aa.len() ==> aa[i] >= 1 && aa[i] < i + 2));
        assert(i + 2 <= n);
    };
}

spec fn build_subordinates_map(n: int, aa: Seq<int>) -> Map<int, int> 
    requires valid_input(n, aa)
    ensures 
        forall|k: int| 0 <= k < n ==> result.dom().contains(k + 1),
        forall|k: int| 0 <= k < n ==> result.index(k + 1) == subordinate_count(aa, k + 1)
{
    Map::new(|k: int|
        if 1 <= k <= n {
            subordinate_count(aa, k)
        } else {
            0
        }
    )
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, aa: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, aa@.map(|i, x| x as int))
    ensures valid_output(n as int, aa@.map(|i, x| x as int), result@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed result variable usage in ensures clause */
    proof {
        lemma_sequence_map_properties(n as int, aa@.map(|i, x| x as int));
    }
    
    let ghost n_int = n as int;
    let ghost ghost_aa = aa@.map(|i, x| x as int);
    let ghost count_map: Map<int, int> = build_subordinates_map(n_int, ghost_aa);
    
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < n as usize
        invariant 
            i >= 0,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == count_map.index(j as int + 1)
        decreases (n as usize) - i
    {
        let ghost boss_id: int = (i as int) + 1;
        let count = count_map.index(boss_id);
        proof {
            assert(count >= 0);
            assert(count <= 255);
        }
        result.push(count as i8);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}