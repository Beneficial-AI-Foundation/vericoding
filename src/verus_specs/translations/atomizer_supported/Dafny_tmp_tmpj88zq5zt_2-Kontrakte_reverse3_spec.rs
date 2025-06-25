pub fn swap3(a: &mut [i32], h: usize, i: usize, j: usize)
    requires(
        h < a.len(),
        i < a.len(),
        j < a.len(),
        i != j && j != h && h != i,
    )
    ensures(|a: &mut [i32]|
        a[h as int] == old(a)[i as int] &&
        a[j as int] == old(a)[h as int] &&
        a[i as int] == old(a)[j as int] &&
        forall|k: int| 0 <= k < old(a).len() && k != h && k != i && k != j ==> a[k] == old(a)[k]
    )
{
}

pub fn testSwap3(a: &mut [i32], h: usize, i: usize, j: usize)
    requires(
        h < a.len(),
        i < a.len(),
        j < a.len(),
        i != j && j != h && h != i,
    )
{
}