pub fn canyon_search(a: &[i32], b: &[i32]) -> (d: nat)
    requires(
        a.len() != 0 && b.len() != 0
    )
    requires(
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    )
    requires(
        forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] <= b[j]
    )
    ensures(|d: nat|
        exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && d == if a[i] < b[j] { (b[j] - a[i]) as nat } else { (a[i] - b[j]) as nat }
    )
    ensures(|d: nat|
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> d <= if a[i] < b[j] { (b[j] - a[i]) as nat } else { (a[i] - b[j]) as nat }
    )
{
}