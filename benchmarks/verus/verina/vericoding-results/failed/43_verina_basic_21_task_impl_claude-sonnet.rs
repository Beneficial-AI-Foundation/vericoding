// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened preconditions and added range bounds proof */
proof fn lemma_subseq_found(sub: Vec<i32>, main: Vec<i32>, pos: usize)
    requires
        pos as int + sub.len() <= main.len(),
        forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[pos as int + j]
    ensures
        is_subseq_at(sub, main, pos as int)
{
}

proof fn lemma_no_subseq_up_to(sub: Vec<i32>, main: Vec<i32>, end: usize)
    requires
        end as int <= main.len(),
        forall|i: int| 0 <= i < end ==> !is_subseq_at(sub, main, i)
    ensures
        !exists|i: int| 0 <= i < end && is_subseq_at(sub, main, i)
{
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow checks and loop bounds with proper invariants */
    if sub.len() == 0 {
        return true;
    }
    
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i = 0;
    let search_limit = main.len() - sub.len();
    
    while i <= search_limit
        invariant
            i <= search_limit + 1,
            search_limit == main.len() - sub.len(),
            sub.len() > 0,
            sub.len() <= main.len(),
            forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k)
        decreases search_limit + 1 - i
    {
        let mut j = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                j <= sub.len(),
                i <= search_limit,
                i + sub.len() <= main.len(),
                matches <==> (forall|k: int| 0 <= k < j ==> sub[k] == main[i as int + k])
            decreases sub.len() - j
        {
            let main_idx = i + j;
            if sub[j] != main[main_idx] {
                matches = false;
                break;
            }
            j += 1;
        }
        
        if matches {
            proof {
                assert(forall|k: int| 0 <= k < sub.len() ==> sub[k] == main[i as int + k]);
                lemma_subseq_found(*sub, *main, i);
            }
            return true;
        }
        
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k <= search_limit ==> !is_subseq_at(*sub, *main, k));
    }
    
    false
}
// </vc-code>

}
fn main() {}