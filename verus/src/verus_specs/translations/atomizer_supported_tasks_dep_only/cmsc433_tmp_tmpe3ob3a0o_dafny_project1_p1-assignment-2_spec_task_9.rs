pub fn NoDups(a: &[int]) -> (noDups: bool)
    requires(
        forall|j: int| 0 < j < a.len() ==> a[j-1] <= a[j] // a sorted
    )
    ensures(|noDups: bool|
        noDups <==> forall|j: int| 1 <= j < a.len() ==> a[j-1] != a[j]
    )
{
}