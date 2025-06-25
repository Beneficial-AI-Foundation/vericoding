pub fn partition(a: &mut [i32]) -> (lo: usize, hi: usize)
    requires(true)
    ensures(|result: (usize, usize)| {
        let (lo, hi) = result;
        0 <= lo <= hi <= a.len() &&
        forall|x: usize| 0 <= x < lo ==> a[x] < 0 &&
        forall|x: usize| lo <= x < hi ==> a[x] == 0 &&
        forall|x: usize| hi <= x < a.len() ==> a[x] > 0
    })
{
}