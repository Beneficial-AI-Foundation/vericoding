// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'B' || s[i] == 'W'
}

spec fn count_segments(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 {
        1int
    } else {
        count_segments(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] != s[s.len() - 2] { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove recursive extension property for count_segments on prefixes */
proof fn lemma_count_segments_extend(s: Seq<char>, k: int)
    requires
        1 <= k,
        k < s.len(),
    ensures
        count_segments(s.subrange(0, k + 1))
            == count_segments(s.subrange(0, k))
                + (if s[k] != s[k - 1] { 1int } else { 0int }),
{
    reveal(count_segments);
    let t = s.subrange(0, k + 1);
    assert(t.len() == k + 1);
    assert(t.len() > 1);

    assert(
        count_segments(t)
        == count_segments(t.subrange(0, t.len() - 1))
            + (if t[t.len() - 1] != t[t.len() - 2] { 1int } else { 0int })
    );

    assert(t.subrange(0, t.len() - 1) == s.subrange(0, k));
    assert(t[t.len() - 1] == s[k]);
    assert(t[t.len() - 2] == s[k - 1]);

    assert(
        count_segments(s.subrange(0, k + 1))
        == count_segments(s.subrange(0, k))
            + (if s[k] != s[k - 1] { 1int } else { 0int })
    );
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires 
        valid_input(s@),
    ensures 
        result >= 0,
        result as int == count_segments(s@) - 1,
        result as int <= s.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices in exec code; relate to specs via casts and helper lemma */
    let n: usize = s.len();
    let mut i: usize = 1usize;
    let mut c: i8 = 0i8;

    proof {
        assert(n as int == s@.len());
        reveal(count_segments);
        assert(count_segments(s@.subrange(0, 1int)) == 1int);
    }

    while i < n
        invariant
            n as int == s@.len(),
            1int <= i as int,
            i as int <= n as int,
            c as int == count_segments(s@.subrange(0, i as int)) - 1int,
            0int <= c as int,
            c as int <= i as int - 1int,
        decreases (n - i) as int
    {
        let k: usize = i;
        if s[k] != s[k - 1] {
            c = c + 1i8;
        }
        i = i + 1usize;
        proof {
            assert(1int <= k as int);
            assert(k as int < s@.len());
            lemma_count_segments_extend(s@, k as int);
            if s[k] != s[k - 1] {
                assert(c as int == count_segments(s@.subrange(0, k as int)) - 1int + 1int);
                assert(count_segments(s@.subrange(0, k as int + 1int))
                        == count_segments(s@.subrange(0, k as int)) + 1int);
                assert(c as int == count_segments(s@.subrange(0, k as int + 1int)) - 1int);
            } else {
                assert(c as int == count_segments(s@.subrange(0, k as int)) - 1int);
                assert(count_segments(s@.subrange(0, k as int + 1int))
                        == count_segments(s@.subrange(0, k as int)) + 0int);
                assert(c as int == count_segments(s@.subrange(0, k as int + 1int)) - 1int);
            }
        }
    }

    proof {
        assert(i == n);
        assert(c as int == count_segments(s@.subrange(0, i as int)) - 1int);
        assert(c as int == count_segments(s@) - 1int);
    }

    let result: i8 = c;
    result
}
// </vc-code>


}

fn main() {}