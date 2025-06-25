pub fn onlineMax(a: &[int], x: int) -> (ghost m: int, p: int)
    requires(1 <= x < a.len())
    requires(a.len() != 0)
    ensures(|ret: (int, int)| x <= ret.1 < a.len())
    ensures(|ret: (int, int)| forall|i: int| 0 <= i < x ==> a[i] <= ret.0)
    ensures(|ret: (int, int)| exists|i: int| 0 <= i < x && a[i] == ret.0)
    ensures(|ret: (int, int)| x <= ret.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < ret.1 ==> a[i] < a[ret.1]))
    ensures(|ret: (int, int)| (forall|i: int| x <= i < a.len() && a[i] <= ret.0) ==> ret.1 == a.len() - 1)
{
}