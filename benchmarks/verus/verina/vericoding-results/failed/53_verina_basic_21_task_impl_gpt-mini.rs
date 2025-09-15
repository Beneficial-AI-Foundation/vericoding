// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple min helper */
spec fn min_i32(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative search returning early to simplify invariants */
    let s = sub.clone();
    let m = main.clone();
    if s.len() > m.len() {
        return false;
    }
    let mut i: int = 0;
    while i <= m.len() - s.len()
        invariant 0 <= i && i <= m.len() - s.len() + 1
        invariant (forall|k: int| (0 <= k && k < i) ==> !is_subseq_at(s.clone(), m.clone(), k))
        decreases m.len() - s.len() + 1 - i
    {
        let mut j: int = 0;
        let mut ok: bool = true;
        while j < s.len() && ok
            invariant 0 <= j && j <= s.len()
            invariant (!ok) || (forall|t: int| (0 <= t && t < j) ==> s[t] == m[i + t])
            decreases s.len() - j
        {
            if s[j] != m[i + j] {
                ok = false;
            }
            j = j + 1;
        }
        if ok {
            proof {
                assert(0 <= i);
                assert(i + s.len() <= m.len());
                assert(j == s.len());
                assert(ok);
                assert((forall|t: int| (0 <= t && t < s.len()) ==> s[t] == m[i + t]));
                assert(is_subseq_at(s.clone(), m.clone(), i));
            }
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}