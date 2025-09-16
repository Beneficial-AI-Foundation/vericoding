// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to lift adjacent strict ordering to arbitrary indices */
proof fn lemma_adjacent_chain(r: Seq<i32>, i: int, j: int)
    requires
        0 <= i < j < r.len(),
        forall|k: int| 1 <= k < r.len() ==> r[k - 1] < r[k],
    ensures
        r[i] < r[j],
    decreases j - i
{
    if j == i + 1 {
        assert(1 <= j < r.len());
        assert(r[j - 1] < r[j]);
    } else {
        lemma_adjacent_chain(r, i, j - 1);
        assert(1 <= j < r.len());
        assert(r[j - 1] < r[j]);
        assert(r[i] < r[j - 1]);
        assert(r[i] < r[j]);
    }
}

/* helper modified by LLM (iteration 3): executable helper that returns whether a Vec contains a value, with spec equality */
fn vec_contains(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures
        b == v@.contains(x),
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < v.len()
        invariant
            i <= v.len(),
            found ==> v@.contains(x),
            !found ==> forall|k: int| 0 <= k < i ==> v@[k] != x,
        decreases v.len() - i
    {
        if v[i] == x {
            found = true;
            proof { assert(v@.contains(x)); }
            break;
        }
        i = i + 1;
    }
    if !found {
        assert(i == v.len());
        assert(forall|k: int| 0 <= k < v.len() ==> v@[k] != x);
        proof { assert(!v@.contains(x)); }
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix forall proof style; build strictly increasing vector of unique values between min/max */
    if s.len() == 0 {
        return Vec::new();
    }

    let mut mn: i32 = s[0];
    let mut mx: i32 = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> mn <= s@[k],
            forall|k: int| 0 <= k < i ==> s@[k] <= mx,
            exists|k: int| 0 <= k < i && s@[k] == mn,
            exists|k: int| 0 <= k < i && s@[k] == mx,
        decreases s.len() - i
    {
        if s[i] < mn { mn = s[i]; }
        if s[i] > mx { mx = s[i]; }
        i = i + 1;
    }
    assert(i == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> mn <= s@[k]);
    assert(forall|k: int| 0 <= k < s.len() ==> s@[k] <= mx);

    let mut r: Vec<i32> = Vec::new();
    let mut val: i32 = mn;
    while val <= mx
        invariant
            s.len() > 0,
            mn <= mx,
            (mn as int) <= (val as int) <= (mx as int) + 1,
            forall|k: int| 0 <= k < r.len() ==> s@.contains(r@[k]),
            forall|t: int| (mn as int) <= t < (val as int) ==> s@.contains(t as i32) ==> r@.contains(t as i32),
            forall|k: int| 1 <= k < r.len() ==> r@[k - 1] < r@[k],
            r.len() == 0 || r@[r.len() - 1] < val,
        decreases ((mx as int) + 1 - (val as int))
    {
        let present = vec_contains(&s, val);
        if present {
            let old_r = r@;
            let old_len = r.len();
            r.push(val);
            proof {
                // r@ == old_r.push(val) by Vec::push postcondition
                lemma_seq_contains_after_push(old_r, val);
                if old_len > 0 {
                    assert(old_r[old_len - 1] < val);
                    assert(r@[old_len - 1] < r@[old_len]);
                }
            }
        }
        val = val + 1;
    }

    proof {
        // Global strict ordering from adjacency
        assert(forall|i2: int, j2: int| 0 <= i2 < j2 < r.len() ==> r@[i2] < r@[j2]));
        assert_forall_by(|i2: int, j2: int| {
            if 0 <= i2 && i2 < j2 && j2 < r.len() {
                lemma_adjacent_chain(r@, i2, j2);
            }
        });

        // Every element of r comes from s (already an invariant)
        assert(forall|k: int| 0 <= k < r.len() ==> s@.contains(r@[k]));

        // Every element of s appears in r
        assert((val as int) == (mx as int) + 1);
        assert(forall|idx: int| 0 <= idx < s.len() ==> r@.contains(s@[idx]));
        assert_forall_by(|idx: int| {
            if 0 <= idx && idx < s.len() {
                let t: int = s@[idx] as int;
                assert((mn as int) <= t);
                assert(t <= (mx as int));
                assert(t < (val as int));
                assert(s@.contains(s@[idx]));
                // From the loop invariant instantiated at t, we have r contains s[idx]
                assert(r@.contains(s@[idx]));
            }
        });
    }

    r
}
// </vc-code>

}
fn main() {}