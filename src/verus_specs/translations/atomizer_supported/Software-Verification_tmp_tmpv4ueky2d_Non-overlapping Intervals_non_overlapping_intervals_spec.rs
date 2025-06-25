pub fn non_overlapping_intervals(intervals: &mut [[i32; 2]]) -> i32
    requires(
        1 <= intervals.len() <= 100000,
        forall|i: usize| 0 <= i < intervals.len() ==> -50000 <= intervals[i][0] <= 50000,
        forall|i: usize| 0 <= i < intervals.len() ==> -50000 <= intervals[i][1] <= 50000,
    )
    ensures(|count: i32| count >= 0)
{
}

pub fn bubble_sort(a: &mut [[i32; 2]])
    requires(true)
    ensures(sorted(a, 0, a.len() as i32 - 1))
{
}

pub open spec fn sorted(a: &[[i32; 2]], l: i32, u: i32) -> bool {
    forall|i: i32, j: i32| 0 <= l <= i <= j <= u < a.len() ==> a[i as usize][1] <= a[j as usize][1]
}

pub open spec fn partitioned(a: &[[i32; 2]], i: i32) -> bool {
    forall|k: i32, k_prime: i32| 0 <= k <= i < k_prime < a.len() ==> a[k as usize][1] <= a[k_prime as usize][1]
}