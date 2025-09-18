// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemmas about Seq push index and last */
proof fn lemma_seq_push_last<T>(s: Seq<T>, x: T)
    ensures s.push(x)[s.len() as int] == x
{
    assert(s.push(x).len() == s.len() + 1);
    assert(s.push(x)[s.len() as int] == x);
}

/* helper modified by LLM (iteration 3): push preserves existing indices */
proof fn lemma_seq_push_preserves_index<T>(s: Seq<T>, x: T, i: nat)
    requires i < s.len()
    ensures s.push(x)[i as int] == s[i as int]
{
    assert(s.push(x)[i as int] == s[i as int]);
}
// </vc-helpers>

// <vc-spec>
fn ogrid(start: f32, stop: f32, n: usize) -> (result: Vec<f32>)
    requires n > 0,
    ensures 
        result.len() == n,
        (n == 1 ==> result[0] == start),
        (n > 1 ==> result[0] == start),
        (n > 1 ==> result[n - 1] == stop),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use ghost views when reasoning about Vec spec, implement push loop and final element */
    let mut v: Vec<f32> = Vec::new();
    v.push(start);
    if n > 1 {
        let mut i: usize = 1;
        while i < n - 1
            invariant
                1 <= i,
                i <= n - 1,
                v.len() == i,
                v@.len() == i as nat,
                v@.len() >= 1,
                v@[0] == start
            decreases ((n - i) as int)
        {
            let ghost old_s = v@;
            v.push(start);
            proof {
                lemma_seq_push_preserves_index::<f32>(old_s, start, 0 as nat);
                assert(v@ == old_s.push(start));
                assert(v@[0] == start);
            }
            i += 1;
        }
        let ghost old_s2 = v@;
        v.push(stop);
        proof {
            lemma_seq_push_last::<f32>(old_s2, stop);
            assert(v@ == old_s2.push(stop));
            assert(v@.len() == old_s2.len() + 1);
            assert(v@[(old_s2.len() as int)] == stop);
        }
        assert(v.len() == n);
        assert(v@[0] == start);
        assert(v[0] == start);
        assert(v[n - 1] == stop);
    } else {
        assert(v.len() == 1);
        assert(v@[0] == start);
        assert(v[0] == start);
    }
    assert(v.len() == n);
    v
}
// </vc-code>

}
fn main() {}