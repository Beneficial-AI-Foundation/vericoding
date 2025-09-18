// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): vector length non-negative predicate */
spec fn vec_len_nonneg<T>(v: &Vec<T>) -> bool {
    v.len() >= 0
}

// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative search for subsequence */
    let n_main: int = main.len();
    let n_sub: int = sub.len();
    if n_sub > n_main {
        false
    } else {
        let lim: int = n_main - n_sub;
        let mut i: int = 0;
        while i <= lim
            invariant
                0 <= i && i <= lim + 1,
            decreases
                lim + 1 - i
        {
            let mut j: int = 0;
            let mut ok: bool = true;
            while j < n_sub
                invariant
                    0 <= j && j <= n_sub,
                decreases
                    n_sub - j
            {
                if main[i + j] != sub[j] {
                    ok = false;
                    break;
                }
                j = j + 1;
            }
            if ok {
                return true;
            }
            i = i + 1;
        }
        false
    }
}

// </vc-code>

}
fn main() {}