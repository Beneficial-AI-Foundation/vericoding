// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): usize->int conversion helper */
spec fn usize_to_int(u: usize) -> int {
    u as int
}

// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize indices and cast to int in proofs */
    if sub.len() > main.len() {
        proof {
            assert(!(exists|k: int| is_subseq_at(*sub, *main, k)));
        }
        return false;
    }
    let lim: usize = main.len() - sub.len();
    let mut i: usize = 0;
    while i <= lim
        invariant
            forall|k: int| 0 <= k < i as int ==> !is_subseq_at(*sub, *main, k),
        decreases (lim as int) - (i as int)
    {
        let mut j: usize = 0;
        let mut match_at: bool = true;
        while j < sub.len()
            invariant
                match_at ==>
                    (forall|k: int| 0 <= k < j as int ==> sub[k as usize] == main[i + k as usize]),
            decreases (sub.len() as int) - (j as int)
        {
            if main[i + j] != sub[j] {
                match_at = false;
                break;
            }
            j = j + 1;
        }
        if match_at {
            proof {
                assert(j == sub.len());
                assert(0 <= i as int && i as int + sub.len() as int <= main.len() as int);
                assert(forall|k: int| 0 <= k < sub.len() as int ==> sub[k as usize] == main[i + k as usize]);
                assert(is_subseq_at(*sub, *main, i as int));
            }
            return true;
        }
        proof {
            assert(j < sub.len());
            assert(main[i + j] != sub[j]);
            assert(!(is_subseq_at(*sub, *main, i as int)));
        }
        i = i + 1;
    }
    proof {
        assert(!(exists|k: int| is_subseq_at(*sub, *main, k)));
    }
    false
}

// </vc-code>

}
fn main() {}