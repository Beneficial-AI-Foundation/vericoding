// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma showing (d / s) * s <= d for s > 0 */
proof fn lemma_div_mul_le(d: int, s: int)
    requires
        s > 0,
    ensures
        (d / s) * s <= d,
{
    let q = d / s;
    let r = d % s;
    assert(0 <= r && r < s);
    assert(d == q * s + r);
    assert(q * s <= d);
}

/* helper modified by LLM (iteration 2): lemma showing k < d/s implies k*s < d for s > 0 */
proof fn lemma_k_lt_div_implies_ks_lt_d(k: int, d: int, s: int)
    requires
        s > 0,
        0 <= k,
        k < d / s,
    ensures
        k * s < d,
{
    let q = d / s;
    let r = d % s;
    assert(0 <= r && r < s);
    assert(d == q * s + r);
    assert(k + 1 <= q);
    let diff = q - k;
    assert(diff >= 1);
    assert(q == k + diff);
    assert(q * s == k * s + diff * s);
    assert(diff * s >= s);
    assert(q * s >= k * s + s);
    assert(q * s > k * s);
    assert(d >= q * s);
    assert(d > k * s);
}

/* helper modified by LLM (iteration 2): monotonicity of multiplication with positive s (a <= b ⇒ a*s <= b*s) */
proof fn lemma_mul_le_mono(a: int, b: int, s: int)
    requires
        s > 0,
        a <= b,
    ensures
        a * s <= b * s,
{
    let t = b - a;
    assert(t >= 0);
    assert(b == a + t);
    assert(b * s == a * s + t * s);
    assert(t * s >= 0);
    assert(a * s <= b * s);
}
// </vc-helpers>

// <vc-spec>
fn mgrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires
        step > 0,
        start < stop,
        n == ((stop as int - start as int) / step as int) as usize,
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] == start as int + i * step as int,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] < stop as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed exec int vars; used ghost/proof ints only; added monotone multiplication lemma usage; proved overflow safety for i8 addition */
    let mut v: Vec<i8> = Vec::new();
    let mut cur: i8 = start;

    while v.len() < n
        invariant
            v@.len() <= n as int,
            cur as int == start as int + v@.len() * (step as int),
            forall|k: int| 0 <= k < v@.len() ==> #[trigger] v@[k] == start as int + k * (step as int),
            forall|k: int| 0 <= k < v@.len() ==> #[trigger] v@[k] < stop as int,
        decreases (n as int) - (v.len() as int)
    {
        let ghost len_before: int = v.len() as int;

        proof {
            assert(len_before >= 0);
            let d = stop as int - start as int;
            let s = step as int;
            assert(s > 0);
            assert(n == (d / s) as usize);
            assert(n as int == d / s);
            assert(len_before < n as int);
            lemma_k_lt_div_implies_ks_lt_d(len_before, d, s);
            assert(start as int + len_before * s < stop as int);
            assert(cur as int == start as int + len_before * s);
        }

        v.push(cur);

        proof {
            let len_after = v.len() as int;
            assert(len_after == len_before + 1);
            assert(v@[len_before] == cur as int);
            assert(v@[len_before] == start as int + len_before * (step as int));
            assert(v@[len_before] < stop as int);
        }

        proof {
            let s = step as int;
            let d = stop as int - start as int;
            let len_after = v.len() as int;
            assert(n as int == d / s);
            assert(len_before < n as int);
            assert(len_after == len_before + 1);
            assert(len_after <= n as int);
            // Show next cur value fits in i8 and matches spec position
            assert(cur as int == start as int + len_before * s);
            assert(cur as int + s == start as int + (len_before + 1) * s);
            assert(cur as int + s == start as int + len_after * s);
            // Bound len_after * s by d using monotonicity and division lemma
            lemma_mul_le_mono(len_after, n as int, s);
            lemma_div_mul_le(d, s);
            assert(len_after * s <= (n as int) * s);
            assert((n as int) * s == (d / s) * s);
            assert((d / s) * s <= d);
            assert(start as int + len_after * s <= start as int + d);
            assert(start as int + d == stop as int);
            assert(cur as int + s <= stop as int);
            // i8 addition safety
            assert(cur as int + s <= i8::MAX as int);
            assert(i8::MIN as int <= cur as int);
            assert(i8::MIN as int <= cur as int + s);
        }

        cur = cur + step;
        proof { assert(cur as int == start as int + (v.len() as int) * (step as int)); }
    }

    v
}
// </vc-code>


}
fn main() {}