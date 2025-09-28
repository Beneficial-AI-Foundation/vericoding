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
/* helper modified by LLM (iteration 5): spec-level minimum of a sequence */
spec fn vec_min_spec(s: Seq<int>) -> int
    requires
        s.len() >= 1,
    ensures
        forall|i: int| 0 <= i < s.len() ==> result <= s[i],
        exists|i: int| 0 <= i < s.len() && result == s[i],
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail_min = vec_min_spec(s.slice(1, s.len()));
        if s[0] <= tail_min { s[0] } else { tail_min }
    }
}

/* helper modified by LLM (iteration 5): spec-level maximum of a sequence */
spec fn vec_max_spec(s: Seq<int>) -> int
    requires
        s.len() >= 1,
    ensures
        forall|i: int| 0 <= i < s.len() ==> result >= s[i],
        exists|i: int| 0 <= i < s.len() && result == s[i],
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail_max = vec_max_spec(s.slice(1, s.len()));
        if s[0] >= tail_max { s[0] } else { tail_max }
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
    /* code modified by LLM (iteration 5): compute runtime min/max as i8 and build r using integer arithmetic; prove relation to spec helpers */

    // Compute runtime minimum and its index
    let mut i: usize = 1usize;
    let mut idx_min: usize = 0usize;
    let mut mn: i8 = *s.get(0).unwrap();
    while i < s.len()
        invariant
            0 <= (i as int) <= s@.len(),
            0 <= (idx_min as int) < s@.len(),
            forall|k: int| 0 <= k < (i as int) ==> mn as int <= s@[k] as int,
        decreases s.len() - i
    {
        let v = *s.get(i).unwrap();
        if v < mn {
            mn = v;
            idx_min = i;
        }
        i = i + 1;
    }

    // Compute runtime maximum and its index
    let mut j: usize = 1usize;
    let mut idx_max: usize = 0usize;
    let mut mx: i8 = *s.get(0).unwrap();
    while j < s.len()
        invariant
            0 <= (j as int) <= s@.len(),
            0 <= (idx_max as int) < s@.len(),
            forall|k: int| 0 <= k < (j as int) ==> mx as int >= s@[k] as int,
        decreases s.len() - j
    {
        let v = *s.get(j).unwrap();
        if v > mx {
            mx = v;
            idx_max = j;
        }
        j = j + 1;
    }

    // runtime integers for arithmetic
    let shift_rt: i64 = -(mn as i64);
    let scale_rt: i64 = (mx as i64) - (mn as i64);
    proof {
        // from the above loops we know mx > mn due to precondition (distinct elements exist)
        assert(scale_rt > 0);
    }

    // Build result vector using runtime integer arithmetic
    let mut r: Vec<i8> = Vec::new();
    let mut k: usize = 0usize;
    while k < s.len()
        invariant
            0 <= (k as int) <= s@.len(),
            r@.len() == (k as int),
            forall|t: int| 0 <= t < (k as int) ==> 0 <= r@[t] as int && r@[t] as int <= 1,
        decreases s.len() - k
    {
        let x_rt = *s.get(k).unwrap() as i64;
        let v_rt = ((x_rt + shift_rt) / scale_rt) as i8;
        r.push(v_rt);
        k = k + 1;
    }

    proof {
        // Relate runtime computed min/max and their indices to spec-level min/max
        let im: int = idx_min as int;
        let jm: int = idx_max as int;
        assert(0 <= im && im < s@.len());
        assert(0 <= jm && jm < s@.len());
        // s@[im] (spec view) corresponds to the runtime element at idx_min
        assert(s@[im] as int == mn as int);
        assert(s@[jm] as int == mx as int);
        // vec_min_spec/vec_max_spec give the minimal/maximal values on the spec sequence
        assert(vec_min_spec(s@) == mn as int);
        assert(vec_max_spec(s@) == mx as int);

        // Define spec-level shift/scale and show properties
        let shift_spec: int = -(mn as int);
        let scale_spec: int = (mx as int) - (mn as int);
        assert(scale_spec > 0);

        // Show that every r element equals affine(s element, shift_spec, scale_spec)
        let mut kk: int = 0;
        while kk < s@.len()
            invariant
                0 <= kk <= s@.len(),
                forall|t: int| 0 <= t < kk ==> r@[t] as int == affine(s@[t] as int, shift_spec, scale_spec),
            decreases s@.len() - kk
        {
            // The runtime computation matches the spec affine expression for each index
            assert(r@[kk] as int == ( (s@[kk] as int + shift_spec) / scale_spec ));
            kk = kk + 1;
        }
    }

    r
}

// </vc-code>


}

fn main() {}