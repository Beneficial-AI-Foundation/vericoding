use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn sum_bound_lemma(sum: i32, max: i32, n: nat, i: nat, a_i: i32)
    requires
        i < n,
        sum <= max * (i as i32),
        a_i <= max,
        sum + a_i <= i32::MAX,
        max * ((i + 1) as i32) <= i32::MAX,
    ensures
        sum + a_i <= max * ((i + 1) as i32),
{
    assert(sum + a_i <= max * (i as i32) + max);
    assert(max * (i as i32) + max == max * (i as i32 + 1)) by {
        assert(max * (i as i32) + max == max * (i as i32) + max * 1);
        assert(max * (i as i32) + max * 1 == max * (i as i32 + 1));
    }
    assert((i + 1) as i32 == i as i32 + 1) by {
        assert(i < i32::MAX as nat);
    }
    assert(max * (i as i32 + 1) == max * ((i + 1) as i32));
}
// </vc-helpers>

// <vc-spec>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            n <= a.len(),
            sum <= max * (i as i32),
            sum >= 0,
            forall|j: int| 0 <= j && j < n ==> a[j] <= max,
            sum + max <= i32::MAX,
            max * (n as i32) <= i32::MAX,
        decreases n - i,
    {
        let a_i = a[i];
        let old_sum = sum;
        sum = sum + a_i;
        proof {
            assert(i < n);
            assert(a[i as int] <= max);
            assert(old_sum == sum - a_i);
            assert(old_sum <= max * (i as i32));
            assert(sum <= old_sum + max);
            assert(sum <= max * (i as i32) + max);
            assert(max * ((i + 1) as i32) <= max * (n as i32));
            assert(sum <= i32::MAX);
            sum_bound_lemma(old_sum, max, n as nat, i as nat, a_i);
        }
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {
}

}