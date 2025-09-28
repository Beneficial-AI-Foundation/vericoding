use vstd::prelude::*;

verus! {

spec fn sum_r(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

spec fn sum_l(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_l(s.subrange(1, s.len() as int))
    }
}

spec fn sum_v(v: Seq<int>, c: int, f: int) -> int {
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}

// <vc-helpers>
// Added helper lemma to relate sum_r on a full subrange to the sum on the whole sequence.
proof fn sum_r_subrange_whole(s: Seq<int>)
    ensures sum_r(s.subrange(0, s.len())) == sum_r(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.len() == 0);
        assert(sum_r(s) == 0);
        assert(sum_r(s.subrange(0, s.len())) == 0);
    } else {
        let k: int = s.len() - 1;
        let s0 = s.subrange(0, k);
        // apply induction hypothesis to s0
        sum_r_subrange_whole(s0);
        // By definition of sum_r on non-empty sequences:
        assert(sum_r(s) == sum_r(s0) + s[s.len() - 1]);
        // And for the full subrange:
        assert(sum_r(s.subrange(0, s.len())) == sum_r(s0) + s.subrange(0, s.len())[s.len() - 1]);
        // The last element of the full subrange equals the last element of s
        assert(s.subrange(0, s.len())[s.len() - 1] == s[s.len() - 1]);
        // combine the equalities
        assert(sum_r(s.subrange(0, s.len())) == sum_r(s));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_elems(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
//ensures sum as int == sum_v(v@.map(|i, x| x as int), 0, v@.len())
// </vc-spec>
// <vc-code>
{
    let seq = v@.map(|_, x| x as int);
    let n: nat = v.len();
    let mut i: nat = 0;
    let mut acc: int = 0;
    while i < n
        invariant i <= n;
        invariant acc == sum_r(seq.subrange(0, i as int));
        decreases n - i
    {
        let xi: i32 = v[i];
        acc = acc + (xi as int);
        i = i + 1;
    }
    assert(i == n);
    assert(n as int == seq.len());
    assert(acc == sum_r(seq.subrange(0, n as int)));
    // use helper lemma to conclude subrange(0,n) equals whole sequence when n == seq.len()
    sum_r_subrange_whole(seq);
    assert(acc == sum_r(seq));
    acc as i32
}
// </vc-code>

fn main() {}

}