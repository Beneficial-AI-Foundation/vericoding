// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma for empty subsequence and fixed preconditions */
proof fn lemma_subseq_check(sub: Vec<i32>, main: Vec<i32>, start: int)
    requires
        0 <= start,
        start + sub.len() <= main.len(),
        forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[start + j],
    ensures
        is_subseq_at(sub, main, start),
{
}

proof fn lemma_no_subseq_beyond(sub: Vec<i32>, main: Vec<i32>, start: int)
    requires
        start >= 0,
        start + sub.len() <= main.len(),
        exists|j: int| 0 <= j < sub.len() && sub[j] != main[start + j],
    ensures
        !is_subseq_at(sub, main, start),
{
}

proof fn lemma_subseq_exists_if_found(sub: Vec<i32>, main: Vec<i32>, pos: int)
    requires
        is_subseq_at(sub, main, pos),
    ensures
        exists|i: int| is_subseq_at(sub, main, i),
{
}

proof fn lemma_empty_subseq(sub: Vec<i32>, main: Vec<i32>)
    requires
        sub.len() == 0,
    ensures
        exists|i: int| is_subseq_at(sub, main, i),
{
    assert(is_subseq_at(sub, main, 0));
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and invariant issues */
    if sub.len() == 0 {
        proof {
            lemma_empty_subseq(*sub, *main);
        }
        return true;
    }
    
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i: usize = 0;
    let max_start = main.len() - sub.len();
    
    while i <= max_start
        invariant
            0 <= i,
            i <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k),
        decreases max_start - i
    {
        let mut j = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                0 <= j,
                j <= sub.len(),
                i + sub.len() <= main.len(),
                matches <==> (forall|k: int| 0 <= k < j ==> sub[k] == main[i + k]),
            decreases sub.len() - j
        {
            if sub[j] != main[i + j] {
                matches = false;
                break;
            }
            j += 1;
        }
        
        if matches {
            proof {
                lemma_subseq_check(*sub, *main, i as int);
                lemma_subseq_exists_if_found(*sub, *main, i as int);
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