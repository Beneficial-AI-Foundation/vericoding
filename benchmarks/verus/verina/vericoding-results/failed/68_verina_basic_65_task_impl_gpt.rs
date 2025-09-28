// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): kept original helper lemmas; added comment for iteration tracking */
proof fn lemma_div_le_self(n: usize, d: usize)
    requires
        1 <= d,
    ensures
        n / d <= n,
{
    let ni = n as int;
    let di = d as int;
    let qi = (n / d) as int;
    let ri = (n % d) as int;
    assert(ni == qi * di + ri);
    assert(ri >= 0);
    assert(di >= 1);
    assert(qi >= 0);
    assert(ni >= qi * di);
    assert(qi * di >= qi);
    assert(ni >= qi);
}

/* helper modified by LLM (iteration 2): kept original helper lemmas; added comment for iteration tracking */
proof fn lemma_guard_implies_square(n: usize, w: usize)
    requires
        1 <= w,
        w <= n / w,
    ensures
        w * w <= n,
{
    let ni = n as int;
    let wi = w as int;
    let qi = (n / w) as int;
    let ri = (n % w) as int;
    assert(ni == qi * wi + ri);
    assert(ri >= 0);
    assert(qi >= wi);
    assert(qi * wi >= wi * wi);
    assert(ni >= qi * wi);
    assert(ni >= wi * wi);
}

/* helper modified by LLM (iteration 2): kept original helper lemmas; added comment for iteration tracking */
proof fn lemma_guard_strict_implies_square_gt(n: usize, w: usize)
    requires
        1 <= w,
        w > n / w,
    ensures
        n < w * w,
{
    let ni = n as int;
    let wi = w as int;
    let qi = (n / w) as int;
    let ri = (n % w) as int;
    assert(ni == qi * wi + ri);
    assert(ri >= 0);
    assert(ri < wi);
    assert(qi < wi);
    assert(qi + 1 <= wi);
    assert(ri <= wi - 1);
    assert(ni <= qi * wi + (wi - 1));
    assert(qi * wi + (wi - 1) == (qi + 1) * wi - 1);
    assert((qi + 1) * wi <= wi * wi);
    assert(ni <= wi * wi - 1);
    assert(ni < wi * wi);
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): ensure usize arguments to helper lemmas by introducing a local usize variable */
    let mut r: usize = 0;
    while r + 1 <= n / (r + 1)
        invariant
            r * r <= n,
            r <= n,
        decreases n - r
    {
        let w: usize = r + 1;
        proof {
            lemma_div_le_self(n, w);
            lemma_guard_implies_square(n, w);
        }
        r = w;
    }
    let w: usize = r + 1;
    proof {
        lemma_guard_strict_implies_square_gt(n, w);
    }
    r
}
// </vc-code>

}
fn main() {}