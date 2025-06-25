pub fn findMax(a: &[int]) -> (pos: usize, maxVal: int)
    requires(a.len() > 0)
    requires(forall|i: int| 0 <= i < a.len() ==> a[i] >= 0)
    ensures(|result: (usize, int)| forall|i: int| 0 <= i < a.len() ==> a[i] <= result.1)
    ensures(|result: (usize, int)| exists|i: int| 0 <= i < a.len() && a[i] == result.1)
    ensures(|result: (usize, int)| 0 <= result.0 < a.len())
    ensures(|result: (usize, int)| a[result.0 as int] == result.1)
{
}