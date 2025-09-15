// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to match requirements */
spec fn matches_at_pos(sub: &Vec<i32>, main: &Vec<i32>, pos: usize) -> bool {
    pos + sub.len() <= main.len() &&
    (forall|j: int| 0 <= j < sub@.len() ==> sub@[j] == main@[pos as int + j])
}

/* helper modified by LLM (iteration 5): proof function for establishing postcondition */
proof fn establish_subseq(sub: Vec<i32>, main: Vec<i32>, pos: usize)
    requires
        pos + sub@.len() <= main@.len(),
        forall|j: int| 0 <= j < sub@.len() ==> sub@[j] == main@[pos as int + j]
    ensures is_subseq_at(sub, main, pos as int)
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
    /* code modified by LLM (iteration 5): fixed loop invariant to use invariant_except_break */
    if sub.len() == 0 {
        proof {
            assert(is_subseq_at(*sub, *main, 0));
        }
        return true;
    }
    
    if main.len() < sub.len() {
        return false;
    }
    
    let mut i: usize = 0;
    let max_start = main.len() - sub.len();
    
    while i <= max_start
        invariant
            0 <= i <= max_start + 1,
            max_start == main.len() - sub.len(),
            sub.len() > 0,
            forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k)
        decreases max_start + 1 - i
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < sub.len()
            invariant
                0 <= j <= sub.len(),
                i <= max_start,
                i + sub.len() <= main.len(),
                found ==> (forall|k: int| 0 <= k < j ==> sub@[k] == main@[i as int + k])
            invariant_except_break
                found <==> (forall|k: int| 0 <= k < j ==> sub@[k] == main@[i as int + k])
            ensures
                found ==> j == sub.len() && (forall|k: int| 0 <= k < sub@.len() ==> sub@[k] == main@[i as int + k])
            decreases sub.len() - j
        {
            if sub[j] != main[i + j] {
                found = false;
                break;
            }
            j += 1;
        }
        
        if found {
            proof {
                assert(forall|k: int| 0 <= k < sub@.len() ==> sub@[k] == main@[i as int + k]);
                establish_subseq(*sub, *main, i);
                assert(is_subseq_at(*sub, *main, i as int));
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