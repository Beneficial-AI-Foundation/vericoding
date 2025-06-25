pub fn replace(v: &mut [i32], x: i32, y: i32)
    ensures(
        forall|k: usize| 0 <= k < old(v).len() && old(v)[k as int] == x ==> v[k as int] == y
    )
    ensures(
        forall|k: usize| 0 <= k < old(v).len() && old(v)[k as int] != x ==> v[k as int] == old(v)[k as int]
    )
{
}