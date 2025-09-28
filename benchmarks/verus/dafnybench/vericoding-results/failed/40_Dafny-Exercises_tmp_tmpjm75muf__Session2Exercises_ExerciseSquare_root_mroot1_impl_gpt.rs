use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_ge1_le_square(a: int)
    requires
        a >= 1,
    ensures
        a <= a * a,
{
    let k = a - 1;
    assert(k >= 0);
    let t = a;
    assert(t == 1 + k);
    assert(t * t - t == t * (t - 1));
    assert(t - 1 == k);
    assert(t * (t - 1) == t * k);
    assert(t == 1 + k);
    assert(t * k == (1 + k) * k);
    assert((1 + k) * k == k + k * k);
    assert(0 <= k * k);
    assert(0 <= k + k * k);
    assert(0 <= t * t - t);
    assert(t <= t * t);
    assert(a <= a * a);
}

proof fn lemma_square_le_implies_le_ge1(a: int, b: int)
    requires
        a >= 1,
        a * a <= b,
    ensures
        a <= b,
{
    lemma_ge1_le_square(a);
    assert(a <= a * a);
    assert(a <= b);
}
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut r: u32 = 0;
    while (((r as int) + 1) * ((r as int) + 1) <= n as int)
        invariant
            (r as int) >= 0,
            (r as int) * (r as int) <= n as int
    {
        let old_r: u32 = r;
        let a: int = (old_r as int) + 1;
        let b: int = n as int;

        assert(((old_r as int) + 1) * ((old_r as int) + 1) <= b);
        assert(a >= 1);
        proof {
            lemma_square_le_implies_le_ge1(a, b);
        }
        assert((old_r as int) + 1 <= n as int);
        assert(n as int <= u32::MAX as int);
        assert((old_r as int) + 1 <= u32::MAX as int);

        r = old_r + 1;

        assert((r as int) == a);
        assert((r as int) * (r as int) <= n as int);
    }
    let ri: int = r as int;
    assert(n as int < (ri + 1) * (ri + 1));
    r
}
// </vc-code>

fn main() {}

}