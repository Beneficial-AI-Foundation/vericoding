// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, l: Seq<int>) -> bool {
    n >= 1 && k >= 1 && l.len() == n && k <= n * (n + 1) / 2
}

spec fn total_identifiers_after_robot(i: int) -> int 
    recommends i >= 0
{
    i * (i + 1) / 2
}

spec fn correct_result(n: int, k: int, l: Seq<int>, result: int) -> bool
    recommends valid_input(n, k, l)
{
    exists|i: int| #[trigger] total_identifiers_after_robot(i) > 0 &&
      1 <= i <= n && 
      total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i) &&
      result == l[k - total_identifiers_after_robot(i - 1) - 1]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_find_robot(n: int, k: int)
    requires
        n >= 1,
        k >= 1,
        k <= n * (n + 1) / 2,
    ensures
        exists|i: int| 1 <= i <= n && total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i),
{
    /* helper modified by LLM (iteration 5): restructured proof without while loop */
    let mut found = false;
    let mut j: int = 1;
    
    assert forall|i: int| 1 <= i <= n implies total_identifiers_after_robot(i) == i * (i + 1) / 2;
    
    // Since k <= n*(n+1)/2 and k >= 1, there must be some robot i where
    // total_identifiers_after_robot(i-1) < k <= total_identifiers_after_robot(i)
    
    // We know total_identifiers_after_robot(0) = 0 < k since k >= 1
    // We know total_identifiers_after_robot(n) = n*(n+1)/2 >= k
    
    // By continuity, there must be some i where the transition happens
    assert(total_identifiers_after_robot(0) == 0);
    assert(total_identifiers_after_robot(n) == n * (n + 1) / 2);
    assert(0 < k);
    assert(k <= n * (n + 1) / 2);
    
    // The existence follows from the fact that the function increases monotonically
    // and we have 0 < k <= n*(n+1)/2
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, l: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, l@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, k as int, l@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation with correct robot finding logic */
    proof {
        lemma_find_robot(n as int, k as int);
    }
    
    let mut i: i8 = 1;
    let mut total: i8 = 0;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total == total_identifiers_after_robot((i - 1) as int) as i8,
            forall|j: int| 1 <= j < i ==> total_identifiers_after_robot(j) < k as int,
            i <= n ==> total < k,
    {
        let next_total = total + i;
        if next_total >= k {
            let offset = k - total - 1;
            assert(total_identifiers_after_robot((i - 1) as int) < k as int);
            assert(k as int <= total_identifiers_after_robot(i as int));
            assert(offset >= 0);
            assert(offset < i);
            assert(offset < l.len());
            return l[offset as usize];
        }
        total = next_total;
        i = i + 1;
    }
    
    assert(false);
    unreached()
}
// </vc-code>


}

fn main() {}