pub fn onlineMax(a: &[int], x: int) -> (ghost m: int, p: int)
    requires(1 <= x < a.len())
    requires(a.len() != 0)
    ensures(|result: (int, int)| x <= result.1 < a.len())
    ensures(|result: (int, int)| forall|i: int| 0 <= i < x ==> a[i] <= result.0)
    ensures(|result: (int, int)| exists|i: int| 0 <= i < x && a[i] == result.0)
    ensures(|result: (int, int)| x <= result.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < result.1 ==> a[i] < a[result.1 as int]))
    ensures(|result: (int, int)| (forall|i: int| x <= i < a.len() && a[i] <= result.0) ==> result.1 == a.len() - 1)
{
}