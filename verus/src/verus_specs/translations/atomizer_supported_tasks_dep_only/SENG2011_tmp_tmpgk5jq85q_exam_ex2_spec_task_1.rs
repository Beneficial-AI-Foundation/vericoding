pub fn Getmini(a: &[i32]) -> usize
    requires a.len() > 0
    ensures |mini: usize| 0 <= mini < a.len()
    ensures |mini: usize| forall|x: usize| 0 <= x < a.len() ==> a[mini] <= a[x]
    ensures |mini: usize| forall|x: usize| 0 <= x < mini ==> a[mini] < a[x]
{
}