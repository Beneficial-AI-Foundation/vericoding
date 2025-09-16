// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn how_many_times(string: Seq<char>, substring: Seq<char>) -> (result:nat)
    decreases string.len(),
{
    if (string.len() == 0) {
        0
    } else if substring.is_prefix_of(string) {
        1 + how_many_times(string.skip(1), substring)
    } else {
        how_many_times(string.skip(1), substring)
    }
}

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): nonempty predicate */
spec fn is_nonempty(s: Seq<char>) -> bool { s.len() >= 1 }
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)

    requires
        substring.len() >= 1,

    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace ints with usize and fix invariants and indexing */
    let s = string@;
    let sub = substring@;
    let m = substring.len();
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < string.len()
        invariant
            (cnt as nat) + how_many_times(s.skip(i as nat), sub) == how_many_times(s, sub),
        decreases s.len() - (i as nat)
    {
        let mut matches: bool = true;
        let mut j: usize = 0;
        if i + substring.len() <= string.len() {
            while j < substring.len()
                invariant
                    (j as nat) <= (m as nat),
                    forall |t: nat| t < (j as nat) ==> s[(i as nat) + t] == sub[t],
                decreases (m as nat) - (j as nat)
            {
                if string[i + j] != substring[j] {
                    matches = false;
                    break;
                }
                j += 1;
            }
            if matches && j == substring.len() {
                cnt += 1;
            }
        }
        i += 1;
    }
    if cnt > (u32::MAX as usize) {
        None
    } else {
        Some(cnt as u32)
    }
}

// </vc-code>

}
fn main() {}