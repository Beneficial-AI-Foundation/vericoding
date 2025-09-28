// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a_1: Seq<int>, a_2: Seq<int>) -> bool {
    n >= 1 &&
    a_1.len() == n && a_2.len() == n &&
    forall|i: int| #![trigger a_1[i], a_2[i]] 0 <= i < n ==> 1 <= a_1[i] <= 100 && 1 <= a_2[i] <= 100
}

spec fn sum_range(s: Seq<int>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len() && forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1
{
    if start >= end { 
        0 
    } else { 
        s[start] + sum_range(s, start + 1, end) 
    }
}

spec fn is_valid_result(n: int, a_1: Seq<int>, a_2: Seq<int>, result: int) -> bool {
    valid_input(n, a_1, a_2) &&
    result >= n + 1 &&
    result <= (n + 1) * 100 &&
    exists|i: int| 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) &&
    forall|i: int| 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): relate Vec index to mapped sequence element */
proof fn vec_index_matches_seq(a: &Vec<i8>, i: int)
    requires 0 <= i < a@.len(),
    ensures a.index(i as nat) as int == (a@.map_values(|x: i8| x as int))@[i],
{
    // The mapped sequence element equals the underlying view element cast to int
    assert((a@.map_values(|x: i8| x as int))@[i] == (a@)@[i] as int);
    assert(a.index(i as nat) as int == (a@)@[i] as int);
}

/* helper modified by LLM (iteration 4): bounds for sum_range slices */
proof fn sum_range_bounds(n: int, a_1: Seq<int>, a_2: Seq<int>, i: int)
    requires valid_input(n, a_1, a_2) && 0 <= i < n,
    ensures n + 1 <= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (n + 1) * 100,
{
    assert(forall|k: int| 0 <= k < i + 1 ==> a_1[k] >= 1);
    assert(forall|k: int| i <= k < n ==> a_2[k] >= 1);
    assert(sum_range(a_1, 0, i + 1) >= i + 1);
    assert(sum_range(a_2, i, n) >= n - i);
    assert(sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) >= (i + 1) + (n - i));
    assert(sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) >= n + 1);

    assert(forall|k: int| 0 <= k < i + 1 ==> a_1[k] <= 100);
    assert(forall|k: int| i <= k < n ==> a_2[k] <= 100);
    assert(sum_range(a_1, 0, i + 1) <= (i + 1) * 100);
    assert(sum_range(a_2, i, n) <= (n - i) * 100);
    assert(sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (i + 1) * 100 + (n - i) * 100);
    assert((i + 1) * 100 + (n - i) * 100 == (n + 1) * 100);
    assert(sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (n + 1) * 100);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a_1: Vec<i8>, a_2: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int))
    ensures is_valid_result(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute maximum split sum using runtime integers and prove spec-level properties in a proof block */
    // Use runtime integers for computation
    let n_i32: i32 = n as i32;

    // initial s1 = a_1[0]
    let mut s1: i32 = 0;
    let mut j: i32 = 0;
    while j < 1
        decreases 1 - j
    {
        s1 = s1 + (a_1[j as usize] as i32);
        j = j + 1;
    }

    // compute prefix sum for a_2 up to 0 (empty)
    let mut s2: i32 = 0;
    let mut k: i32 = 0;
    while k < n_i32
        decreases n_i32 - k
    {
        s2 = s2 + (a_2[k as usize] as i32);
        k = k + 1;
    }

    let mut best: i32 = s1 + s2;
    let mut arg: i32 = 0;

    let mut i_rt: i32 = 1;
    while i_rt < n_i32
        decreases n_i32 - i_rt
    {
        // compute s1_i = sum a_1[0..i_rt+1)
        let mut s1_i: i32 = 0;
        let mut j2: i32 = 0;
        while j2 < i_rt + 1
            decreases i_rt + 1 - j2
        {
            s1_i = s1_i + (a_1[j2 as usize] as i32);
            j2 = j2 + 1;
        }

        // compute s2_i = sum a_2[i_rt..n)
        let mut s2_i: i32 = 0;
        let mut k2: i32 = i_rt;
        while k2 < n_i32
            decreases n_i32 - k2
        {
            s2_i = s2_i + (a_2[k2 as usize] as i32);
            k2 = k2 + 1;
        }

        let val: i32 = s1_i + s2_i;
        if val > best {
            best = val;
            arg = i_rt;
        }
        i_rt = i_rt + 1;
    }

    // Recompute final sums for arg to make the link explicit at runtime
    let mut s1_final: i32 = 0;
    let mut j3: i32 = 0;
    while j3 < arg + 1
        decreases arg + 1 - j3
    {
        s1_final = s1_final + (a_1[j3 as usize] as i32);
        j3 = j3 + 1;
    }

    let mut s2_final: i32 = 0;
    let mut k3: i32 = arg;
    while k3 < n_i32
        decreases n_i32 - k3
    {
        s2_final = s2_final + (a_2[k3 as usize] as i32);
        k3 = k3 + 1;
    }

    // Ensure best matches the recomputed final sums
    best = s1_final + s2_final;

    let result: i8 = best as i8;

    // Proof block: relate runtime computations to spec-level sequences and prove postcondition
    proof {
        let n_int: int = n as int;
        let seq1 = a_1@.map_values(|x: i8| x as int);
        let seq2 = a_2@.map_values(|x: i8| x as int);

        // Reconstruct the same maximization using spec integers to obtain arg_spec and best_spec
        let mut best_spec: int = 0;
        let mut arg_spec: int = 0;

        // initial values: compute prefix 0..1 and suffix 0..n
        let mut s1_spec: int = 0;
        let mut jj: int = 0;
        while jj < 1
            invariant
                0 <= jj <= 1,
                s1_spec == sum_range(seq1, 0, jj),
            decreases 1 - jj
        {
            vec_index_matches_seq(&a_1, jj);
            s1_spec = s1_spec + (a_1.index(jj as nat) as int);
            jj = jj + 1;
        }

        let mut s2_spec: int = 0;
        let mut kk: int = 0;
        while kk < n_int
            invariant
                0 <= kk <= n_int,
                s2_spec == sum_range(seq2, 0, kk),
            decreases n_int - kk
        {
            vec_index_matches_seq(&a_2, kk);
            s2_spec = s2_spec + (a_2.index(kk as nat) as int);
            kk = kk + 1;
        }

        best_spec = s1_spec + s2_spec;
        arg_spec = 0;

        let mut ii: int = 1;
        while ii < n_int
            invariant
                1 <= ii <= n_int,
                forall|t: int| 0 <= t < ii ==> best_spec >= sum_range(seq1, 0, t + 1) + sum_range(seq2, t, n_int),
            decreases n_int - ii
        {
            // compute s1_i
            let mut s1_i_spec: int = 0;
            let mut jj2: int = 0;
            while jj2 < ii + 1
                invariant
                    0 <= jj2 <= ii + 1,
                    s1_i_spec == sum_range(seq1, 0, jj2),
                decreases ii + 1 - jj2
            {
                vec_index_matches_seq(&a_1, jj2);
                s1_i_spec = s1_i_spec + (a_1.index(jj2 as nat) as int);
                jj2 = jj2 + 1;
            }

            // compute s2_i
            let mut s2_i_spec: int = 0;
            let mut kk2: int = ii;
            while kk2 < n_int
                invariant
                    ii <= kk2 <= n_int,
                    s2_i_spec == sum_range(seq2, ii, kk2),
                decreases n_int - kk2
            {
                vec_index_matches_seq(&a_2, kk2);
                s2_i_spec = s2_i_spec + (a_2.index(kk2 as nat) as int);
                kk2 = kk2 + 1;
            }

            let val_spec: int = s1_i_spec + s2_i_spec;
            if val_spec > best_spec {
                best_spec = val_spec;
                arg_spec = ii;
            }
            ii = ii + 1;
        }

        // Recompute final sums for arg_spec to get explicit equality
        let mut s1_final_spec: int = 0;
        let mut j_final: int = 0;
        while j_final < arg_spec + 1
            invariant
                0 <= j_final <= arg_spec + 1,
                s1_final_spec == sum_range(seq1, 0, j_final),
            decreases arg_spec + 1 - j_final
        {
            vec_index_matches_seq(&a_1, j_final);
            s1_final_spec = s1_final_spec + (a_1.index(j_final as nat) as int);
            j_final = j_final + 1;
        }

        let mut s2_final_spec: int = 0;
        let mut k_final: int = arg_spec;
        while k_final < n_int
            invariant
                arg_spec <= k_final <= n_int,
                s2_final_spec == sum_range(seq2, arg_spec, k_final),
            decreases n_int - k_final
        {
            vec_index_matches_seq(&a_2, k_final);
            s2_final_spec = s2_final_spec + (a_2.index(k_final as nat) as int);
            k_final = k_final + 1;
        }

        assert(best_spec == s1_final_spec + s2_final_spec);

        // now relate runtime result to best_spec: runtime best was computed by identical arithmetic
        assert(result as int == best_spec);

        // use helper to show bounds
        sum_range_bounds(n_int, seq1, seq2, arg_spec);

        // existence and bounds are now established
        assert(is_valid_result(n_int, seq1, seq2, result as int));
    }

    result
}

// </vc-code>


}

fn main() {}