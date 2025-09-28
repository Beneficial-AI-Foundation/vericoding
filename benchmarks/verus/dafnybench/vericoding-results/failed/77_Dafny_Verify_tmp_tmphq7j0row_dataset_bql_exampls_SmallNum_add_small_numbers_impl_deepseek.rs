use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_commutes(a: int, b: int)
    ensures
        a * b == b * a,
{
}

proof fn lemma_sum_bound(a: Seq<i32>, n: int, max: i32)
    requires
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        a.subrange(0, n).sum() <= max * (n as int),
{
    lemma_sum_bound_rec(a, n, max, 0, 0);
}

proof fn lemma_sum_bound_rec(a: Seq<i32>, n: int, max: i32, i: int, sum: int)
    requires
        n > 0,
        n <= a.len(),
        forall|j: int| 0 <= j && j < n ==> a[j] <= max,
        0 <= i,
        i <= n,
        sum == a.subrange(0, i).sum(),
    ensures
        sum <= max * i,
{
    if i < n {
        assert(a[i] <= max);
        lemma_sum_bound_rec(a, n, max, i + 1, sum + a[i] as int);
        assert(sum + a[i] as int <= max * i + max);
        assert(max * i + max == max * (i + 1));
    }
}

proof fn lemma_idx_bounds(idx: usize, n: usize)
    requires
        idx < n,
    ensures
        0 <= idx as int && idx as int < n as int,
{
}
// </vc-helpers>
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
    let mut idx: usize = 0;
    
    while idx < n
        invariant
            idx <= n,
            sum == a@.subrange(0, idx as int).sum(),
            sum <= max * (idx as i32),
    {
        lemma_idx_bounds(idx, n);
        assert(a[idx] <= max) by {
            assert(0 <= idx as int && idx as int < n as int);
        };
        sum = sum + a[idx];
        idx = idx + 1;
        
        assert(sum <= max * (idx as i32)) by {
            let idx_int: int = idx as int;
            lemma_mul_commutes(max as int, idx_int);
        };
    }
    
    assert(sum <= max * (n as i32)) by {
        let n_int: int = n as int;
        lemma_sum_bound(a@, n_int, max);
    };
    
    sum
}
// </vc-code>

fn main() {
}

}