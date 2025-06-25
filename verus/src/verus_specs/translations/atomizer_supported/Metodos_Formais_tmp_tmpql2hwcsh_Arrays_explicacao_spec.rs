pub fn buscar(a: &[int], x: int) -> (r: int)
    ensures(r < 0 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x)
    ensures(0 <= r < a.len() ==> a[r] == x)
{
}