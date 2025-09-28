use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers needed for this proof)
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut i: int = 1;
    let mut cur_max: i32 = a[0];
    let mut cur_min: i32 = a[0];
    while i < n
        invariant (0 <= i && i <= n)
        invariant (forall |k: int| (0 <= k && k < i) ==> (a[k as usize] <= cur_max && a[k as usize] >= cur_min))
        invariant (cur_min <= cur_max)
    {
        let old_max: i32 = cur_max;
        let old_min: i32 = cur_min;
        let v: i32 = a[i as usize];
        if v > old_max {
            cur_max = v;
        } else if v < old_min {
            cur_min = v;
        }
        proof {
            // old_min <= old_max holds from the loop invariant at start of iteration
            assert(old_min <= old_max);

            // monotonicity of cur_max and cur_min
            if v > old_max {
                assert(cur_max == v);
                // cur_max = v > old_max
                assert(old_max < cur_max);
                assert(old_max <= cur_max);
            } else {
                assert(cur_max == old_max);
                assert(old_max <= cur_max);
            }
            if v < old_min {
                assert(cur_min == v);
                // cur_min = v < old_min
                assert(cur_min <= old_min);
            } else {
                assert(cur_min == old_min);
                assert(cur_min <= old_min);
            }

            // From the loop invariant before the update (with old_max/old_min),
            // we have bounds for all k < i
            assert(forall |k: int| (0 <= k && k < i) ==>
                (a[k as usize] <= old_max && a[k as usize] >= old_min)
            );

            // For k < i, combine with monotonicity to get bounds with new cur_max/cur_min
            assert(forall |k: int| (0 <= k && k < i) ==>
                (a[k as usize] <= cur_max && a[k as usize] >= cur_min)
            );

            // Now handle k == i (the newly included element)
            if v > old_max {
                // cur_max == v and cur_min == old_min
                assert(cur_max == a[i as usize]);
                // need to show a[i] >= cur_min
                assert(old_min <= old_max);
                assert(old_max < v);
                assert(old_min < v);
                assert(a[i as usize] >= cur_min);
            } else if v < old_min {
                // cur_min == v and cur_max == old_max
                assert(cur_min == a[i as usize]);
                // need to show a[i] <= cur_max
                assert(old_min > v);
                assert(old_min <= old_max);
                assert(v <= old_max);
                assert(a[i as usize] <= cur_max);
            } else {
                // old_min <= v <= old_max, and cur_min <= old_min <= old_max <= cur_max
                assert(old_min <= v);
                assert(v <= old_max);
                assert(cur_min <= old_min);
                assert(old_max <= cur_max);
                assert(a[i as usize] <= cur_max);
                assert(a[i as usize] >= cur_min);
            }

            // Combine k < i and k == i to get bounds for k < i+1
            assert(forall |k: int| (0 <= k && k < i + 1) ==>
                (a[k as usize] <= cur_max && a[k as usize] >= cur_min)
            );

            // cur_min <= cur_max is preserved
            assert(cur_min <= cur_max);
        }
        i += 1;
    }
    let diff: i32 = cur_max - cur_min;
    proof {
        // From the loop invariant at i == n we have bounds for all elements
        assert(forall |k: int| (0 <= k && k < n) ==> (a[k as usize] <= cur_max && a[k as usize] >= cur_min));
        // Now for any indices ii, jj within bounds show the required inequality
        assert(forall |ii: int, jj: int|
            (0 <= ii && ii < n && 0 <= jj && jj < n) ==>
            (a[ii as usize] - a[jj as usize] <= diff)
        );
    }
    diff
}
// </vc-code>

fn main() {
}

}