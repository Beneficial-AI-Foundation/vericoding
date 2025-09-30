// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] && s[i] <= 'z'
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate stating that every element is 'x' */
spec fn all_x(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'x'
}

/* helper modified by LLM (iteration 4): lemma preserving all_x when pushing 'x' */
proof fn lemma_all_x_push_x(s: Seq<char>)
    requires
        all_x(s)
    ensures
        all_x(s.push('x'))
{
    assert(s.push('x').len() == s.len() + 1);
    assert forall |i: int|
        0 <= i < s.push('x').len()
        implies
        s.push('x')[i] == 'x'
    by
    {
        if i < s.len() {
            assert(s.push('x')[i] == s[i]);
        } else {
            assert(i == s.len());
            assert(s.push('x')[i] == 'x');
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): build a Vec of same length as s filled with 'x' using usize counter */
    let n: usize = s.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    proof { assert(all_x(res@)); }
    while i < n
        invariant
            i <= n,
            res@.len() == i as nat,
            all_x(res@),
        decreases (n - i) as nat
    {
        let ghost old_seq = res@;
        res.push('x');
        proof {
            lemma_all_x_push_x(old_seq);
            assert(res@ == old_seq.push('x'));
            assert(all_x(res@));
        }
        i = i + 1;
    }
    proof {
        assert(res@.len() == i as nat);
        assert(i == n);
        assert(res@.len() == n as nat);
        assert(s@.len() == s.len() as nat);
        assert(res@.len() == s@.len());
    }
    res
}
// </vc-code>


}

fn main() {}