pub fn non_overlapping_intervals(intervals: &mut Array2<i32>) -> (count: i32)
    requires(
        1 <= intervals.len_0() <= 100000,
        intervals.len_1() == 2,
        forall|i: usize| 0 <= i < intervals.len_0() ==> -50000 <= intervals[i, 0] <= 50000,
        forall|i: usize| 0 <= i < intervals.len_0() ==> -50000 <= intervals[i, 1] <= 50000,
    )
    ensures(count >= 0)
{
}

pub fn bubble_sort(a: &mut Array2<i32>)
    requires(a.len_1() == 2)
    ensures(sorted(a, 0, a.len_0() - 1))
{
}

pub fn sorted(a: &Array2<i32>, l: i32, u: i32) -> bool
    requires(a.len_1() == 2)
{
    forall|i: i32, j: i32| 0 <= l <= i <= j <= u < a.len_0() ==> a[i, 1] <= a[j, 1]
}