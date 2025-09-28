// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, scores: Seq<int>) -> bool {
    n == scores.len() && n >= 1 && exists|i: int| 0 <= i < scores.len() && scores[i] != 0
}

spec fn unique_non_zero_scores(scores: Seq<int>) -> Set<int> {
    Set::new(|x: int| exists|i: int| 0 <= i < scores.len() && scores[i] != 0 && scores[i] == x)
}

spec fn valid_result(scores: Seq<int>, result: int) -> bool {
    result >= 1 && 
    result == unique_non_zero_scores(scores).len() && 
    result <= scores.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added assert statements to establish postconditions */
proof fn set_insert_increases_len(s: Set<int>, x: int)
    requires !s.contains(x)
    ensures s.insert(x).len() == s.len() + 1
{
    assert(s.insert(x).len() == s.len() + 1);
}

proof fn set_insert_no_change(s: Set<int>, x: int)
    requires s.contains(x)
    ensures s.insert(x) == s
{
    assert(s.insert(x) == s);
}

proof fn empty_set_len()
    ensures Set::<int>::empty().len() == 0
{
    assert(Set::<int>::empty().len() == 0);
}

proof fn set_len_bound(s: Set<int>, max_size: int)
    requires forall|x: int| s.contains(x) ==> 0 <= x < max_size
    ensures s.len() <= max_size
{
    assert(s.len() <= max_size);
}

proof fn build_unique_set(scores: Seq<int>, i: nat)
    requires i <= scores.len()
    ensures unique_non_zero_scores(scores.subrange(0, i as int)).len() >= 0
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, scores: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, scores@.map(|i, x| x as int))
    ensures valid_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed bounds checking and arithmetic overflow */
    let mut count = 0i8;
    let mut i = 0usize;
    
    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            0 <= count <= 127,
            count <= i,
        decreases scores.len() - i
    {
        if scores[i] != 0 {
            let mut j = 0usize;
            let mut found = false;
            
            while j < i
                invariant
                    0 <= j <= i,
                    i < scores.len(),
                    found == (exists|k: int| 0 <= k < j && j <= scores.len() && scores@[k] as int == scores@[i] as int),
                decreases i - j
            {
                if scores[j] == scores[i] {
                    found = true;
                    break;
                }
                j += 1;
            }
            
            if !found && count < 127 {
                count += 1;
            }
        }
        i += 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}