// RUN: %verus "%s"

use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, s: int, t: int) -> int
    recommends 0 <= s <= t <= a.len()
    decreases t - s when 0 <= s <= t <= a.len()
{
    if s == t { 0 } else { sum(a, s, t-1) + a[t-1] }
}

// <vc-helpers>
use vstd::prelude::*;
use vstd::invariant::*;

#[verifier(nonlinear)] 
proof fn lemma_sum_monotonic(a: Seq<int>, s: int, t: int, u: int)
    requires 0 <= s <= t <= u <= a.len()
    ensures sum(a, s, t) + sum(a, t, u) == sum(a, s, u)
    decreases u - s
{
    if s == u {
        assert(sum(a, s, t) + sum(a, t, u) == 0 + 0);
        assert(sum(a, s, u) == 0);
    } else if t == u {
        assert(sum(a, s, t) + sum(a, t, u) == sum(a, s, t) + 0);
        assert(sum(a, s, u) == sum(a, s, t));
    } else {
        assert(sum(a, s, u) == sum(a, s, u - 1) + a[u - 1]);
        assert(sum(a, t, u) == sum(a, t, u - 1) + a[u - 1]);
        lemma_sum_monotonic(a, s, t, u-1);
        assert(sum(a, s, t) + sum(a, t, u - 1) == sum(a, s, u - 1));
        assert(sum(a, s, t) + sum(a, t, u) == sum(a, s, u));
    }
}
// </vc-helpers>

// <vc-spec>
fn max_seg_sum(a: &Vec<int>) -> (result: (usize, usize))
    ensures ({
        let (k, m) = result;
        &&& k <= m <= a.len()
        &&& forall |p: int, q: int| 0 <= p <= q <= a.len() ==> 
            sum(a@, p, q) <= sum(a@, k as int, m as int)
    })
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return (0, 0);
    }

    let mut max_so_far: int = 0;
    let mut current_max: int = 0;
    let mut start_idx: usize = 0;
    let mut end_idx: usize = 0;
    let mut current_start: usize = 0;

    let a_seq = a@;

    max_so_far = sum(a_seq, 0, 1);
    current_max = sum(a_seq, 0, 1);
    start_idx = 0;
    end_idx = 1;
    current_start = 0;

    if a_seq[0] < 0 {
        current_max = 0;
        current_start = 1;
    }


    let mut i: usize = 1;
    while i < n {
        invariant(
            0 < i <= n,
            (forall |p: int, q: int| 0 <= p <= q <= i ==> sum(a_seq, p, q) <= max_so_far),
            max_so_far == sum(a_seq, start_idx as int, end_idx as int),
            (0 <= start_idx as int <= end_idx as int <= i as int),
            current_max == sum(a_seq, current_start as int, i as int),
            (0 <= current_start as int <= i as int),
            (forall |p: int| 0 <= p && p <= i ==> {
                &&& #[trigger] sum(a_seq, p, i) <= current_max
                &&& (current_max <= 0 ==> #[trigger] sum(a_seq, p, i) <= 0)
            }),
        );
        {
            let val = a[i];
            let next_current_max_candidate = current_max + val;

            let prev_current_max = current_max;
            let prev_current_start = current_start;

            if next_current_max_candidate > val {
                current_max = next_current_max_candidate;
            } else {
                current_max = val;
                current_start = i;
            }

            proof {
                let i_int = i as int;
                let i_plus_1: int = (i+1) as int;


                if prev_current_max + val > val {
                    assert(prev_current_max == sum(a_seq, prev_current_start as int, i_int));
                    lemma_sum_monotonic(a_seq, prev_current_start as int, i_int, i_plus_1);
                    assert(sum(a_seq, prev_current_start as int, i_plus_1) == sum(a_seq, prev_current_start as int, i_int) + a_seq[i]);
                    assert(current_max == sum(a_seq, prev_current_start as int, i_plus_1));
                    assert(current_start == prev_current_start);
                } else {
                    lemma_sum_monotonic(a_seq, i_int, i_int, i_plus_1);
                    assert(sum(a_seq, i_int, i_plus_1) == sum(a_seq, i_int, i_int) + a_seq[i]);
                    assert(sum(a_seq, i_int, i_plus_1) == 0 + a_seq[i]); // sum(a, s, s) is 0
                    assert(current_max == sum(a_seq, i_int, i_plus_1));
                    assert(current_start == i);
                }

                assert(current_max == sum(a_seq, current_start as int, i_plus_1));

                assert(for_all |p: int| 0 <= p && p <= i_int ==> {
                    if prev_current_max > 0 {
                        #[trigger] sum(a_seq, p, i_int) <= prev_current_max
                    } else {
                        #[trigger] sum(a_seq, p, i_int) <= 0
                    }
                });

                assert( forall |p: int| 0 <= p && p <= i_plus_1-1 ==> {
                    let p_int = p as int;
                    lemma_sum_monotonic(a_seq, p_int, i_int, i_plus_1);
                    sum(a_seq, p_int, i_plus_1) == sum(a_seq, p_int, i_int) + a_seq[i]
                });

                assert( forall |p: int| 0 <= p && p <= i_plus_1 ==> {
                    if current_max > 0 {
                        if p == i_plus_1 { // p == i+1
                            0 <= current_max
                        } else {
                            if prev_current_max + val > val { // we extended
                                sum(a_seq, p, i_int) <= prev_current_max;
                                sum(a_seq, p, i_plus_1) <= prev_current_max + a_seq[i];
                                sum(a_seq, p, i_plus_1) <= current_max
                            } else { // we reset
                                sum(a_seq, p, i_int) <= 0;
                                sum(a_seq, p, i_plus_1) <= 0 + a_seq[i];
                                sum(a_seq, p, i_plus_1) <= current_max
                            }
                        }
                    } else { // current_max <= 0
                        if p == i_plus_1 { // p == i+1
                            0 <= 0
                        } else {
                            if prev_current_max + val > val { // we extended
                                sum(a_seq, p, i_int) <= prev_current_max;
                                sum(a_seq, p, i_plus_1) <= prev_current_max + a_seq[i];
                                sum(a_seq, p, i_plus_1) <= current_max
                            } else { // we reset
                                sum(a_seq, p, i_int) <= 0;
                                sum(a_seq, p, i_plus_1) <= 0 + a_seq[i];
                                sum(a_seq, p, i_plus_1) <= current_max
                            }
                        }
                    }
                });

            }


            if current_max > max_so_far {
                max_so_far = current_max;
                start_idx = current_start;
                end_idx = i + 1;
            }
            
            // Proof for `max_so_far` invariant update:
            proof {
                let i_int = i as int;
                let i_plus_1 = (i + 1) as int; // This is the new upper bound of the loop invariant.
                // We need to show `forall |p: int, q: int| 0 <= p <= q <= i_plus_1 ==> sum(a_seq, p, q) <= max_so_far`.

                assert( forall |p: int, q: int| 0 <= p <= q <= i ==> sum(a_seq, p, q) <= max_so_far@ );

                assert( forall |p: int| 0 <= p && p <= i_plus_1 ==> sum(a_seq, p, i_plus_1) <= current_max@ );

                assert( forall |p: int, q: int| 
                    0 <= p <= q <= i_plus_1 ==> {
                        if q <= i {
                            sum(a_seq, p, q) <= max_so_far@
                        } else if q == i_plus_1 {
                            sum(a_seq, p, i_plus_1) <= current_max@
                        } else {
                            true
                        }
                    }
                );
                // The above assertion is not strong enough. We need to show `sum(a_seq, p, q) <= max_so_far`
                // for all 0 <= p <= q <= i+1.
                // Case 1: q <= i. This comes from the previous invariant.
                // Case 2: q = i + 1. We know `sum(a_seq, p, i+1) <= current_max`.
                // If `current_max` replaced `max_so_far`, then `current_max` is the new `max_so_far`,
                // and the assertion holds. If not, then `current_max <= max_so_far@`, so it also holds.

                assert( forall |p: int, q: int| 0 <= p <= q <= i_plus_1 ==> sum(a_seq, p, q) <= max_so_far );
            }
        }
        i += 1;
    }

    let (k_final, m_final) = (start_idx, end_idx);

    proof {
        assert(start_idx as int <= end_idx as int <= n as int);
        assert(forall |p: int, q: int| 0 <= p <= q <= n as int ==> sum(a_seq, p, q) <= max_so_far);
        assert(max_so_far == sum(a_seq, start_idx as int, end_idx as int));
    }

    (k_final, m_final)
}
// </vc-code>

fn main() {}

}