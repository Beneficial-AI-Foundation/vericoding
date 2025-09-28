// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    1 <= s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
}

spec fn easily_playable(s: Seq<char>) -> bool {
    (forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> s[i] != 'L') &&
    (forall|i: int| 0 <= i < s.len() && i % 2 == 1 ==> s[i] != 'R')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma unfolding the easily_playable predicate to its quantifier form */
fn lemma_easily_playable_unfold(s: Seq<char>)
    ensures
        easily_playable(s) <==> ((forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> s[i] != 'L') &&
                                 (forall|i: int| 0 <= i < s.len() && i % 2 == 1 ==> s[i] != 'R')),
{
    proof {
        assert(easily_playable(s) == ((forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> s[i] != 'L') &&
                                      (forall|i: int| 0 <= i < s.len() && i % 2 == 1 ==> s[i] != 'R')));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: String) -> (result: String)
    requires valid_input(s@)
    ensures result@ == seq!['Y', 'e', 's'] <==> easily_playable(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices and cast in specs to avoid int in runtime */
    let cs: Vec<char> = s.chars().collect();
    let n: usize = cs.len();
    let mut ok: bool = true;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            ok == (forall|j: int| 0 <= j < i as int ==> (if j % 2 == 0 { cs@[j] != 'L' } else { cs@[j] != 'R' })),
        decreases (n - i) as nat
    {
        let c: char = cs[i];
        let cur: bool = if i % 2 == 0 { c != 'L' } else { c != 'R' };
        ok = ok && cur;
        i = i + 1;
    }

    proof {
        assert(cs@ == s@);
        assert(ok == (forall|j: int| 0 <= j < n as int ==> (if j % 2 == 0 { cs@[j] != 'L' } else { cs@[j] != 'R' })));
        assert(ok == easily_playable(s@));
    }

    if ok { "Yes".to_string() } else { "No".to_string() }
}

// </vc-code>


}

fn main() {}