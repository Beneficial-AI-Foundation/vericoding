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
    if sub.len() > main.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= main.len() - sub.len()
        invariant
            i <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !is_subseq_at(*sub, *main, k),
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                j <= sub.len(),
                matches <==> forall|k: int| 0 <= k < j ==> sub[k] == main[i + k],
        {
            if sub[j] != main[i + j] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            assert(is_subseq_at(*sub, *main, i as int));
            return true;
        }
        
        i = i + 1;
    }
    
    assert(forall|k: int| 0 <= k <= main.len() - sub.len() ==> !is_subseq_at(*sub, *main, k));
    assert(forall|k: int| k > main.len() - sub.len() ==> !is_subseq_at(*sub, *main, k)) by {
        if main.len() - sub.len() < 0 {
            assert(forall|k: int| !is_subseq_at(*sub, *main, k));
        }
    }
    
    false
}
// </vc-code>

}
fn main() {}