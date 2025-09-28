// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove swapping preserves occurrence counts */
proof fn lemma_swap_preserves_count(s: Seq<i32>, i: int, j: int, x: i32)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        count_occurrences(s.update(i, s[j]).update(j, s[i]), x) == count_occurrences(s, x),
    decreases s.len()
{
    if i == j {
        assert(s.update(i, s[j]).update(j, s[i]) =~= s);
        return;
    }
    
    let swapped = s.update(i, s[j]).update(j, s[i]);
    
    // We need to prove count_occurrences(swapped, x) == count_occurrences(s, x)
    // by induction on the sequence
    
    if s.len() == 0 {
        return;
    }
    
    if i == 0 && j == 0 {
        return;
    } else if i == 0 {
        // Swap involves first element
        if x == s[j] {
            // The element at j moves to position 0
            assert(swapped[0] == s[j]);
            assert(count_occurrences(swapped.skip(1), x) == count_occurrences(s.skip(1).update(j-1, s[0]), x));
        } else if x == s[0] {
            // The element at 0 moves to position j
            assert(swapped[0] == s[j]);
            assert(count_occurrences(swapped.skip(1), x) == count_occurrences(s.skip(1).update(j-1, s[0]), x));
        }
    } else if j == 0 {
        lemma_swap_preserves_count(s, j, i, x);
    } else {
        // Neither i nor j is 0
        assert(swapped[0] == s[0]);
        lemma_swap_preserves_count(s.skip(1), i-1, j-1, x);
        assert(count_occurrences(swapped.skip(1), x) == count_occurrences(s.skip(1), x));
    }
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
    /* code modified by LLM (iteration 5): fixed view operator usage by capturing it before proof block */
    let mut result = a.clone();
    let n = result.len();
    
    if n == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == a.len(),
            result.len() == n,
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < l < i ==> #[trigger] result[k] <= #[trigger] result[l],
            forall|k: int, l: int| 0 <= k < i && i <= l < n ==> #[trigger] result[k] <= #[trigger] result[l],
            forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x),
        decreases n - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                result.len() == n,
                i < n,
                i + 1 <= j <= n,
                i <= min_idx < j,
                forall|k: int| i <= k < j ==> result[min_idx as int] <= result[k],
                forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x),
            decreases n - j
        {
            if result[j] < result[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let ghost old_result = result@;
            let temp = result[i];
            result.set(i, result[min_idx]);
            result.set(min_idx, temp);
            
            proof {
                assert(result@ =~= old_result.update(i as int, old_result[min_idx as int]).update(min_idx as int, old_result[i as int]));
                assert forall|x: i32| count_occurrences(result@, x) == count_occurrences(old_result, x) by {
                    lemma_swap_preserves_count(old_result, i as int, min_idx as int, x);
                }
                assert forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x) by {
                    assert(count_occurrences(old_result, x) == count_occurrences(a@, x));
                }
            }
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}