use vstd::prelude::*;

verus! {

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>
fn sum_invariant(a: &[i32], i: usize, sum: i32) -> bool {
    (0 <= i && i <= a.len()) && (sum as int == compute_sum(a, 0, i as i32))
}

fn max_invariant(a: &[i32], i: usize, max: i32) -> bool {
    (0 <= i && i <= a.len()) && (max as int == compute_max(a, 0, i as i32))
}

spec fn compute_sum(a: &[i32], start: i32, end: i32) -> int
    requires 0 <= start <= end <= a.len() as i32
    decreases end - start
{
    if start == end {
        0
    } else {
        a[start as usize] as int + compute_sum(a, start + 1, end)
    }
}

spec fn compute_max(a: &[i32], start: i32, end: i32) -> int
    requires 0 <= start <= end <= a.len() as i32
    decreases end - start
{
    if start == end {
        if a.len() == 0 { 0 } else { a[0] as int }
    } else {
        let current = a[start as usize] as int;
        let sub_max = compute_max(a, start + 1, end);
        if current > sub_max { current } else { sub_max }
    }
}

proof fn sum_max_relation(a: &[i32], i: i32, sum: int, max: int)
    requires
        0 <= i <= a.len() as i32,
        sum == compute_sum(a, 0, i),
        max == compute_max(a, 0, i),
        forall|k: i32| 0 <= k < a.len() as i32 ==> 0 <= a[k as usize] as int,
    ensures
        sum <= i * max
    decreases i
{
    if i == 0 {
        assert(sum == 0);
        assert(sum <= 0 * max);
    } else {
        let prev_sum = compute_sum(a, 0, i - 1);
        let prev_max = compute_max(a, 0, i - 1);
        sum_max_relation(a, i - 1, prev_sum, prev_max);
        assert(sum == prev_sum + a[(i - 1) as usize] as int);
        assert(max >= prev_max);
        assert(max >= a[(i - 1) as usize] as int);
        assert(prev_sum <= (i - 1) * prev_max);
        assert(sum <= (i - 1) * max + max);
        assert(sum <= i * max);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn M(N: int, a: &[int]) -> (result: (int, int))
    requires 
        0 <= N,
        a.len() == N,
        forall|k: int| 0 <= k && k < N ==> 0 <= a[k],
    ensures 
        result.0 <= N * result.1;
// </vc-spec>
// </vc-spec>

// <vc-code>
fn compute_sum_max(N: usize, a: &[i32]) -> (result: (i32, i32))
    requires 
        a.len() == N,
        forall|k: usize| 0 <= k < N ==> 0 <= a[k],
    ensures 
        result.0 as int <= (N as int) * (result.1 as int)
{
    let mut sum: i32 = 0;
    let mut max: i32 = if N == 0 { 0 } else { a[0] };
    let mut i: usize = 0;

    while i < N
        invariant
            0 <= i <= N,
            sum_invariant(a, i, sum),
            max_invariant(a, i, max),
            forall|k: usize| 0 <= k < N ==> 0 <= a[k]
    {
        sum = sum + a[i];
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }

    proof {
        sum_max_relation(a, N as i32, sum as int, max as int);
    }

    (sum, max)
}
// </vc-code>

fn main() {}

}