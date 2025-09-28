// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow, bounds, and loop logic */
    let sub_len = sub.len();
    let main_len = main.len();
    
    if sub_len > main_len {
        return false;
    }
    
    if sub_len == 0 {
        assert(is_subseq_at(*sub, *main, 0));
        return true;
    }
    
    let mut i: usize = 0;
    while i <= main_len - sub_len
        invariant
            0 <= i,
            i <= main_len,
            sub_len <= main_len,
            i <= main_len - sub_len + 1,
            forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k),
        decreases main_len - sub_len - i + 1
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < sub_len
            invariant
                0 <= i,
                i <= main_len - sub_len,
                sub_len <= main_len,
                0 <= j,
                j <= sub_len,
                i + j <= main_len,
                found <==> forall|k: int| 0 <= k < j ==> sub[k] == main[i + k],
            decreases sub_len - j
        {
            if sub[j] != main[i + j] {
                found = false;
                j = j + 1;
                break;
            }
            j = j + 1;
        }
        
        if found && j == sub_len {
            assert(forall|k: int| 0 <= k < sub_len ==> sub[k] == main[i + k]);
            assert(is_subseq_at(*sub, *main, i as int));
            return true;
        }
        
        i = i + 1;
    }
    
    assert(i > main_len - sub_len);
    assert(forall|k: int| 0 <= k <= main_len - sub_len ==> !is_subseq_at(*sub, *main, k));
    assert(forall|k: int| k > main_len - sub_len ==> k + sub_len > main_len ==> !is_subseq_at(*sub, *main, k));
    
    false
}
// </vc-code>

}
fn main() {}