use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<i32>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        sum(v, i, (j - 1) as int) + v[(j - 1) as int] as int
    }
}

spec fn sum_max_to_right(v: Seq<i32>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}



spec fn sum2(v: Seq<i32>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        v[i] as int + sum2(v, i + 1, j)
    }
}

//Now do the same but with a loop from right to left
spec fn sum_max_to_right2(v: Seq<i32>, j: int, i: int, s: int) -> bool //maximum sum stuck to the right
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

// <vc-helpers>
spec fn sum_max_to_right_inclusive(v: Seq<i32>, j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

proof fn lemma_sum2_monotonic_prefix(v: Seq<i32>, a: int, b: int, c: int)
    requires 0 <= a <= b <= c <= v.len()
    ensures sum2(v, a, c) == sum2(v, a, b) + sum2(v, b, c)
    decreases c - a
{
    if a == c {
        assert(sum2(v,a,c) == 0);
        assert(sum2(v,a,b) == 0);
        assert(sum2(v,b,c) == 0);
    } else {
        if a == b {
            assert(sum2(v,a,b) == 0);
            assert(sum2(v,a,c) == sum2(v,b,c));
        } else if b == c {
            assert(sum2(v,b,c) == 0);
            assert(sum2(v,a,c) == sum2(v,a,b));
        } else {
            assert(sum2(v,a,c) == v[a] + sum2(v,a+1,c));
            assert(sum2(v,a,b) == v[a] + sum2(v,a+1,b));
            lemma_sum2_monotonic_prefix(v, a + 1, b, c);
            assert(sum2(v,a+1,c) == sum2(v,a+1,b) + sum2(v,b,c)); 
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn seg_suma_maxima2(v: &[i32], i: usize) -> (result: (i32, usize))
    requires v.len() > 0 && i < v.len()
    ensures 
        0 <= result.1 <= i && 
        result.0 as int == sum2(v@, result.1 as int, (i + 1) as int) && 
        sum_max_to_right2(v@, 0, i as int, result.0 as int)
//Implement and verify
// </vc-spec>
// <vc-code>
{
    let mut current_sum: i32 = v[i as usize]; // Represents sum of v[current_start_idx..i]
    let mut current_start_idx: usize = i;     // Start index for `current_sum`
    let mut max_sum_val: i32 = v[i as usize]; // Overall maximum sum found so far ending at `i`
    let mut max_sum_idx: usize = i;           // Start index for `max_sum_val`

    // `k_iter` iterates from `i-1` down to `0`. `k_iter` is the index of element being processed.
    let mut k_iter: int = (i as int) - 1; 

    while k_iter >= 0
        invariant
            // Loop bounds for `k_iter`
            -1 <= k_iter < i, 

            // `max_sum_val` represents `sum2(v@, max_sum_idx, (i + 1) as int)`
            // And it is the maximum among all `sum2(v@, l, i + 1)` where `k_iter + 1 <= l <= i`
            max_sum_val as int == sum2(v@, max_sum_idx as int, (i + 1) as int),
            0 <= max_sum_idx <= i,
            ({
                let mut temp_max_sum: int = v[i] as int;
                let mut temp_max_idx: int = i as int;
                let mut j: int = i - 1;
                while j >= k_iter + 1
                    invariant
                        j >= k_iter,
                        ({
                            let mut current_sub_sum: int = v[i] as int;
                            let mut current_j: int = i as int;
                            let mut current_start: int = i as int;
                            while current_j >= j
                                invariant
                                    current_j >= j - 1,
                                    current_start <= current_j + 1,
                                    current_j <= i,
                                    current_sub_sum == sum2(v@, current_start, current_j + 1),
                                decreases current_j
                            {
                                if v[current_j as usize] as int > current_sub_sum + (v[current_j as usize] as int) {
                                    current_sub_sum = v[current_j as usize] as int;
                                    current_start = current_j;
                                } else {
                                    current_sub_sum = current_sub_sum + (v[current_j as usize] as int);
                                }
                                current_j = current_j - 1;
                            }
                            current_sub_sum >= temp_max_sum
                        }),
                        ({
                            let mut current_sub_sum: int = v[i] as int;
                            let mut current_j: int = i as int;
                            let mut current_start: int = i as int;
                            while current_j >= j
                                invariant
                                    current_j >= j - 1,
                                    current_start <= current_j + 1,
                                    current_j <= i,
                                    current_sub_sum == sum2(v@, current_start, current_j + 1),
                                decreases current_j
                            {
                                if v[current_j as usize] as int > current_sub_sum + (v[current_j as usize] as int) {
                                    current_sub_sum = v[current_j as usize] as int;
                                    current_start = current_j;
                                } else {
                                    current_sub_sum = current_sub_sum + (v[current_j as usize] as int);
                                }
                                current_j = current_j - 1;
                            }
                            temp_max_sum == current_sub_sum
                        }),
                    decreases i - j
                {
                    let mut current_sub_sum: int = v[i] as int;
                    let mut current_start: int = i as int;
                    proof {
                        lemma_sum2_monotonic_prefix(v@, j, i, i + 1);
                    }
                    if v[j as usize] as int > current_sub_sum + (v[j as usize] as int) { // Placeholder values
                        current_sub_sum = v[j as usize] as int;
                        current_start = j;
                    } else {
                        current_sub_sum = current_sub_sum + (v[j as usize] as int);
                    }

                    if current_sub_sum > temp_max_sum {
                        temp_max_sum = current_sub_sum;
                        temp_max_idx = current_start;
                    }
                    j = j - 1;
                }
                max_sum_val as int == temp_max_sum
            }),

            // `current_sum` represents `sum2(v@, current_start_idx, (i + 1) as int)`
            // And it is the maximum among all `sum2(v@, l, i + 1)` where `current_start_idx <= l <= i`
            // AND the elements summed must form a contiguous subarray ending at `i`.
            current_sum as int == sum2(v@, current_start_idx as int, (i + 1) as int),
            (k_iter as usize) < current_start_idx <= i,

        decreases k_iter
    {
        // `val_at_k` is the value of the element `v[k_iter]`
        let val_at_k: i32 = v[k_iter as usize];

        let sum_if_extend = val_at_k + current_sum;

        if (sum_if_extend) > (val_at_k) {
            proof {
                lemma_sum2_monotonic_prefix(v@, k_iter, current_start_idx as int, i + 1);
                assert(sum2(v@, k_iter, current_start_idx as int) == val_at_k as int);
                assert(sum2(v@, k_iter, i + 1) == sum2(v@, k_iter, current_start_idx as int) + sum2(v@, current_start_idx as int, i + 1));
                assert(sum2(v@, k_iter, i + 1) == (val_at_k as int) + (current_sum as int));
            }
            current_sum = sum_if_extend;
            current_start_idx = k_iter as usize; // If extended forward, the new start is k_iter.
        } else {
            // It's better to start a new segment from `k_iter`.
            current_sum = val_at_k;
            current_start_idx = k_iter as usize;
            proof {
                lemma_sum2_monotonic_prefix(v@, k_iter, k_iter + 1, i + 1);
                assert(current_sum as int == sum2(v@, current_start_idx as int, (i + 1) as int));
            }
        }

        // After updating `current_sum` and `current_start_idx`, check if it's the new overall maximum.
        if current_sum > max_sum_val {
            max_sum_val = current_sum;
            max_sum_idx = current_start_idx;
        }

        k_iter = k_iter - 1;
    }

    (max_sum_val, max_sum_idx)
}
// </vc-code>

fn main() {}

}