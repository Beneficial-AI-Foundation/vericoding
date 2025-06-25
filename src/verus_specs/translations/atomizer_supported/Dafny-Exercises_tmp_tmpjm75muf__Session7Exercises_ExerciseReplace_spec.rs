pub fn replace(v: &mut [i32], x: i32, y: i32)
    ensures(
        forall|k: usize| 0 <= k < old(v).len() && old(v)[k] == x ==> v[k] == y
    )
    ensures(
        forall|k: usize| 0 <= k < old(v).len() && old(v)[k] != x ==> v[k] == old(v)[k]
    )
{
}