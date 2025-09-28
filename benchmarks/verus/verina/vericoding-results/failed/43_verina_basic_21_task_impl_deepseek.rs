// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_subseq_at_implies_exists(sub: Vec<i32>, main: Vec<i32>, i: int)
    requires
        0 <= i && i + sub.len() <= main.len(),
        forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j]
    ensures
        exists|k: int| is_subseq_at(sub, main, k)
{
    /* helper modified by LLM (iteration 5): Direct proof using given parameters */
    assert(is_subseq_at(sub, main, i));
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic bounds and loop invariants */
    let mut i: usize = 0;
    let main_len = main.len();
    let sub_len = sub.len();
    
    while i <= main_len.checked_sub(sub_len).unwrap_or(main_len)
        invariant
            0 <= i <= main_len - sub_len + 1,
            forall|k: int| 0 <= k < i as int ==> !is_subseq_at(*sub, *main, k)
        decreases main_len - i
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < sub_len
            invariant
                0 <= j <= sub_len,
                found == (forall|k: int| 0 <= k < j as int ==> sub[k] == main[i + k])
            decreases sub_len - j
        {
            if sub[j] != main[i + j] {
                found = false;
                break;
            }
            j += 1;
        }
        
        if found && j == sub_len {
            proof {
                lemma_subseq_at_implies_exists(*sub, *main, i as int);
            }
            return true;
        }
        
        i += 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}