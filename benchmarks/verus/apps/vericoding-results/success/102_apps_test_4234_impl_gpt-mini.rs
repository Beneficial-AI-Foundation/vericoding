// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 0
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() % 2 == 0 && forall|i: int| 0 <= i < s.len() / 2 ==> #[trigger] s[2*i] != #[trigger] s[2*i+1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): seq_even checks seq length even */
spec fn seq_even(s: Seq<char>) -> bool {
    s.len() % 2 == 0
}

/* helper modified by LLM (iteration 5): pairs_neq_prop asserts unequal adjacent pairs for complete pairs */
spec fn pairs_neq_prop(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() / 2 ==> #[trigger] s[2*i] != #[trigger] s[2*i+1]
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: (usize, Vec<char>))
    requires 
        valid_input(n as int, s@),
    ensures 
        result.0 >= 0,
        result.0 == s@.len() - result.1@.len(),
        is_good_string(result.1@),
        result.0 + result.1@.len() == s@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): greedy build longest good subsequence */
    let mut t: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            s@.len() == n as int,
            t@.len() <= i as int,
            pairs_neq_prop(t@),
        decreases n - i
    {
        let ch = s[i];
        if t.len() % 2 == 0 {
            t.push(ch);
        } else {
            let last = t[t.len() - 1];
            if last != ch {
                t.push(ch);
            } else {
                // skip ch to avoid equal pair
            }
        }
        i += 1;
    }

    // If odd length, pop the last to make even
    if t.len() % 2 == 1 {
        let _ = t.pop();
    }

    let deletions: usize = n - t.len();

    proof {
        assert(s@.len() == n as int);
        assert(t@.len() <= n as int);
        assert(t@.len() % 2 == 0);
        assert(pairs_neq_prop(t@));
        assert((deletions as int) == s@.len() - t@.len());
    }

    (deletions, t)
}
// </vc-code>


}

fn main() {}