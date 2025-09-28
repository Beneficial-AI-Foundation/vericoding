// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn affine(x: int, shift: int, scale: int) -> int {
    if scale > 0 { (x + shift) / scale } else { 0 }
}

spec fn affine_seq(s: Seq<int>, r: Seq<int>, shift: int, scale: int) -> bool {
    scale > 0 && r.len() == s.len() &&
    forall|i: int| 0 <= i < s.len() ==> #[trigger] r[i] == #[trigger] affine(s[i], shift, scale)
}
// </vc-preamble>

// <vc-helpers>
proof fn div_zero_when_lt(n: int, d: int)
    requires
        d > 0,
        0 <= n,
        n < d,
    ensures
        n / d == 0,
{
}

proof fn div_self_is_one(d: int)
    requires
        d > 0,
    ensures
        d / d == 1,
{
}

proof fn affine_unit_value(min: int, max: int, x: int)
    requires
        min < max,
        min <= x,
        x <= max,
    ensures
        (x - min) / (max - min) == if x == max { 1 } else { 0 },
{
    let d = max - min;
    assert(d > 0);
    if x == max {
        assert((x - min) == d);
        div_self_is_one(d);
    } else {
        assert(min <= x && x < max);
        let n = x - min;
        assert(0 <= n);
        assert(n < d);
        div_zero_when_lt(n, d);
    }
}

proof fn min_lt_max_from_bounds_and_distinct(s: Seq<int>, min: int, max: int)
    requires
        s.len() >= 2,
        forall|k: int| 0 <= k < s.len() ==> min <= s[k] && s[k] <= max,
        exists|k: int| 0 <= k < s.len() && s[k] == min,
        exists|k: int| 0 <= k < s.len() && s[k] == max,
        exists|i: int, j: int| 0 <= i < j < s.len() && s[i] != s[j],
    ensures
        min < max,
{
    let kmin = choose|k: int| 0 <= k < s.len() && s[k] == min;
    let kmax = choose|k: int| 0 <= k < s.len() && s[k] == max;
    assert(min <= max) by {
        assert(min <= s[kmax]);
        assert(s[kmax] <= max);
    }
    if !(min < max) {
        assert(min == max);
        assert(forall|k: int| 0 <= k < s.len() ==> s[k] == min) by {
            assert(forall|k: int| 0 <= k < s.len() ==> min <= s[k] && s[k] <= max);
            assert(min == max);
        }
        let i = choose|i: int| 0 <= i < s.len();
        let j = choose|j: int| 0 <= j < s.len();
        assert(exists|i2: int, j2: int| 0 <= i2 < j2 < s.len() && s[i2] != s[j2]);
    }
}

// </vc-helpers>

// <vc-spec>
fn rescale_to_unit(s: Vec<i8>) -> (r: Vec<i8>)
    requires s@.len() >= 2,
             exists|i: int, j: int| (0 <= i < j < s@.len()) && s@[i] != s@[j]
    ensures r@.len() == s@.len(),
            forall|i: int| 0 <= i < s@.len() ==> 0 <= r@[i] as int && r@[i] as int <= 1,
            exists|i: int| 0 <= i < s@.len() && r@[i] as int == 0,
            exists|i: int| 0 <= i < s@.len() && r@[i] as int == 1,
            ({
                let s_int = s@.map(|i, x| x as int);
                let r_int = r@.map(|i, x| x as int);
                exists|shift: int, scale: int| affine_seq(s_int, r_int, shift, scale) && scale > 0
            })
// </vc-spec>
// <vc-code>
{
    let n_usize: usize = s.len();
    let n: int = n_usize as int;

    // First pass: compute min and max over s
    let mut minv: i8 = s[0];
    let mut maxv: i8 = s[0];
    let mut i: usize = 1;
    while i < n_usize
        invariant
            1 <= i as int <= n,
            s@.len() == n,
            exists|k: int| 0 <= k < i as int && s@[k] == minv as int,
            exists|k: int| 0 <= k < i as int && s@[k] == maxv as int,
            forall|k: int| 0 <= k < i as int ==> (minv as int) <= s@[k] && s@[k] <= (maxv as int),
        decreases n - i as int
    {
        let x = s[i];
        if x < minv { minv = x; }
        if x > maxv { maxv = x; }
        i += 1;
    }

    // From preconditions and bounds, deduce min < max on ints
    proof {
        min_lt_max_from_bounds_and_distinct(
            s@, minv as int, maxv as int,
            );
    }

    // Second pass: build r with 1 at max positions, 0 otherwise
    let mut r: Vec<i8> = Vec::new();
    let mut j: usize = 0;
    while j < n_usize
        invariant
            r@.len() == j as int,
            0 <= j as int <= n,
            s@.len() == n,
            forall|k: int| 0 <= k < j as int ==> r@[k] as int == if s@[k] == maxv as int { 1 } else { 0 },
        decreases n - j as int
    {
        let x = s[j];
        let val: i8 = if x == maxv { 1 } else { 0 };
        r.push(val);
        j += 1;
    }

    // Prove elements are within 0..1
    proof {
        assert(forall|k: int| 0 <= k < n ==> 0 <= r@[k] as int && r@[k] as int <= 1) by {
            assert(forall|k: int| 0 <= k < n ==> r@[k] as int == if s@[k] == maxv as int { 1 } else { 0 });
        };
    }

    // Prove existence of indices with 1 and 0
    proof {
        // There exists an index equal to maxv and to minv from first pass invariants
        assert(exists|k: int| 0 <= k < n && s@[k] == maxv as int);
        assert(exists|k: int| 0 <= k < n && s@[k] == minv as int);
        // r matches mapping everywhere
        assert(forall|k: int| 0 <= k < n ==> r@[k] as int == if s@[k] == maxv as int { 1 } else { 0 });
        // Hence 1 exists
        assert(exists|k: int| 0 <= k < n && r@[k] as int == 1);
        // And 0 exists since min < max implies minv != maxv
        assert(minv as int < maxv as int);
        assert(exists|k: int| 0 <= k < n && r@[k] as int == 0);
    }

    // Prove affine relation existence
    proof {
        let shift: int = -(minv as int);
        let scale: int = (maxv as int) - (minv as int);
        assert(scale > 0);
        // r equals affine(s, shift, scale)
        assert(forall|k: int| 0 <= k < n ==> r@[k] as int == affine(s@[k] as int, shift, scale)) by {
            assert(forall|k: int| 0 <= k < n ==> r@[k] as int == if s@[k] == maxv as int { 1 } else { 0 });
            assert(scale > 0);
            assert(forall|k: int| 0 <= k < n ==> (minv as int) <= s@[k] && s@[k] <= (maxv as int));
            assert(forall|k: int| 0 <= k < n ==> (s@[k] as int + shift) / scale == (s@[k] as int - (minv as int)) / scale);
            assert(forall|k: int| 0 <= k < n ==> (s@[k] as int - (minv as int)) / scale == if s@[k] == maxv as int { 1 } else { 0 }) by {
                assert(minv as int < maxv as int);
                assert(forall|k: int| 0 <= k < n ==> (minv as int) <= s@[k] && s@[k] <= (maxv as int));
                // The helper lemma gives the exact value
                // The SMT can instantiate per k using affine_unit_value
            };
        };
        // Wrap into affine_seq witness
        assert(exists|sh: int, sc: int| affine_seq(s@.map(|i, x| x as int), r@.map(|i, x| x as int), sh, sc) && sc > 0) by {
            let sh = shift;
            let sc = scale;
            assert(sc > 0);
            assert(affine_seq(s@.map(|i, x| x as int), r@.map(|i, x| x as int), sh, sc));
        };
    }

    r
}
// </vc-code>


}

fn main() {}