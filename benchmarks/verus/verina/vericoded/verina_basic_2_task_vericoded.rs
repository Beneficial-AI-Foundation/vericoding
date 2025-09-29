// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple transitivity lemma for <= with empty body as SMT can discharge it */
proof fn le_trans(a: int, b: int, c: int)
    requires
        a <= b,
        b <= c
    ensures
        a <= c
{
}

// </vc-helpers>

// <vc-spec>
fn find_smallest(s: &Vec<nat>) -> (result: Option<nat>)
    ensures
        match result {
            None => s.len() == 0,
            Some(r) => s.len() > 0 && 
                      (exists|i: int| 0 <= i < s.len() && s[i] == r) &&
                      (forall|i: int| 0 <= i < s.len() ==> r <= s[i])
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): linear scan using exec variables only; spec reasoning confined to invariants */
    if s.len() == 0usize {
        return None;
    }
    let n: usize = s.len();
    let mut i: usize = 1usize;
    let mut min: nat = s[0usize];
    while i < n
        invariant
            s.len() == n,
            n >= 1usize,
            1usize <= i && i <= n,
            exists|j: int| 0 <= j && j < i as int && s[j] == min,
            forall|k: int| 0 <= k && k < i as int ==> min <= s[k],
        decreases (n - i) as int
    {
        let v: nat = s[i];
        if v < min {
            min = v;
        }
        i += 1usize;
    }
    Some(min)
}
// </vc-code>

}
fn main() {}