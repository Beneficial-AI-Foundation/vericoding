use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        sum(v, i, (j-1) as int) + v[(j-1) as int]
    }
}

spec fn sum_max_to_right(v: Seq<int>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}

spec fn sum2(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        v[i as int] + sum2(v, (i+1) as int, j)
    }
}

spec fn sum_max_to_right2(v: Seq<int>, j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

// <vc-helpers>
lemma fn lemma_sum_relation(v: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum(v, i, k) == sum(v, i, j) + sum(v, j, k)
    decreases k - j
{
    if j < k {
        lemma_sum_relation(v, i, j, (k - 1) as int);
        assert(sum(v, i, k) == sum(v, i, (k-1) as int) + v[(k-1) as int]);
        assert(sum(v, i, j) + sum(v, j, k) == sum(v, i, j) + sum(v, j, (k-1) as int) + v[(k-1) as int]);
    }
}

lemma fn lemma_sum2_relation(v: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum2(v, i, k) == sum2(v, i, j) + sum2(v, j, k)
    decreases j - i
{
    if i < j {
        lemma_sum2_relation(v, (i + 1) as int, j, k);
        assert(sum2(v, i, k) == v[i as int] + sum2(v, (i+1) as int, k));
        assert(sum2(v, i, j) + sum2(v, j, k) == v[i as int] + sum2(v, (i+1) as int, j) + sum2(v, j, k));
    }
}

lemma fn lemma_sum_equals_sum2(v: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures sum(v, i, j) == sum2(v, i, j)
    decreases j - i
{
    if i < j {
        lemma_sum_equals_sum2(v, i, (j-1) as int);
        lemma_sum_equals_sum2(v, (i+1) as int, j);
        assert(sum(v, i, j) == sum(v, i, (j-1) as int) + v[(j-1) as int]);
        assert(sum2(v, i, j) == v[i as int] + sum2(v, (i+1) as int, j));
        lemma_sum_relation(v, i, (i+1) as int, j); // (i+1) - i = 1
        lemma_sum2_relation(v, i, (i+1) as int, j);

        // a (a+1) (j) => sum(a,j) = sum(a, a+1) + sum(a+1, j) = v[a] + sum(a+1,j)
        // (i) (j-1) (j) => sum(i,j) = sum(i, j-1) + sum(j-1, j) = sum(i, j-1) + v[j-1]
        // sum(v,i,j) == sum2(v,i,j)
        // sum(v, i, j-1) + v[j-1] == v[i] + sum2(v, i+1, j)
        // by inductive hypothesis:
        // sum2(v, i, j-1) + v[j-1] == v[i] + sum2(v, i+1, j)
        // sum2(v, i, j-1) = v[i] + sum2(v, i+1, j-1)
        // so we need to prove:
        // v[i] + sum2(v, i+1, j-1) + v[j-1] == v[i] + sum2(v, i+1, j)
        // which simplifies to:
        // sum2(v, i+1, j-1) + v[j-1] == sum2(v, i+1, j)
        // This is true by definition of sum2 and lemma_sum2_relation
    }
}
// </vc-helpers>

// <vc-spec>
fn seg_max_sum(v: &[i32], i: usize) -> (i32, usize)
    requires v.len() > 0 && i < v.len()
    ensures |result: (i32, usize)|
        result.1 <= i && 
        result.0 == sum(v@.map_values(|x: i32| x as int), result.1 as int, (i+1) as int) &&
        sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, result.0 as int)
// </vc-spec>
// <vc-code>
{
    let v_int = v@.map_values(|x: i32| x as int);

    let mut max_so_far: i32 = v[i];
    let mut current_sum_end_at_i: i32 = v[i];
    let mut start_idx_of_max_sum: usize = i;

    let mut k = i; // Initialize k for the invariant check

    #[invariant]
    while k > 0
        invariant k <= i
        invariant start_idx_of_max_sum <= i
        invariant max_so_far as int == sum(v_int, start_idx_of_max_sum as int, (i + 1) as int)
        invariant k <= start_idx_of_max_sum || (k == start_idx_of_max_sum + 1) // Corrected invariant
        invariant current_sum_end_at_i as int == sum(v_int, k as int, (i + 1) as int) // Corrected invariant from k+1 to k
        invariant forall|l: int, ss: int| #[trigger] (sum(v_int, l, ss)) && k as int <= l <= i as int && ss == i + 1 ==> sum(v_int, l, ss) <= max_so_far as int // Corrected start to k
        decreases k
    {
        k = k - 1;

        let next_sum = current_sum_end_at_i + v[k];

        proof {
            assert(current_sum_end_at_i as int == sum(v_int, (k + 1) as int, (i + 1) as int));
            lemma_sum_relation(v_int, k as int, (k + 1) as int, (i + 1) as int);
            assert(sum(v_int, k as int, (i + 1) as int) == sum(v_int, k as int, (k + 1) as int) + sum(v_int, (k + 1) as int, (i + 1) as int));
            assert(sum(v_int, k as int, (k + 1) as int) == v_int[k as int]);
            assert(next_sum as int == sum(v_int, k as int, (i + 1) as int));
        }

        if next_sum > max_so_far {
            max_so_far = next_sum;
            start_idx_of_max_sum = k;
        }

        current_sum_end_at_i = next_sum;

        proof {
            // Case 1: `l == k`.
            // `sum(v_int, k, i+1)` is `current_sum_end_at_i`.
            // If `next_sum` (which is `current_sum_end_at_i` here) became the new `max_so_far`,
            // then `current_sum_end_at_i == max_so_far`.
            // If not (`next_sum <= old(max_so_far)`), then `max_so_far` is unchanged and
            // `current_sum_end_at_i <= old(max_so_far) == max_so_far`.
            assert(sum(v_int, k as int, (i + 1) as int) <= max_so_far as int);

            // Case 2: `l > k`, i.e., `k + 1 <= l <= i`.
            // From the previous iteration invariant, for any `l'` where `old(k) <= l' <= i`,
            // `sum(v_int, l', i+1) <= old(max_so_far)`.
            // Since `old(k)` is `k+1`, it means for `k+1 <= l <= i`,
            // `sum(v_int, l, i+1) <= old(max_so_far)`.
            // We know `max_so_far >= old(max_so_far)` (it either stayed the same or increased).
            // Therefore, `sum(v_int, l, i+1) <= old(max_so_far) <= max_so_far`.
            assert(forall|l: int, ss: int| #[trigger] (sum(v_int, l, ss)) && (k + 1) as int <= l <= i as int && ss == i + 1 ==> sum(v_int, l, ss) <= max_so_far as int);
        }
    }

    (max_so_far, start_idx_of_max_sum)
}
// </vc-code>

fn main() {
}

}