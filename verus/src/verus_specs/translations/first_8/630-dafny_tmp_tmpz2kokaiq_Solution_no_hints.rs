spec fn sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

pub fn BinarySearch(a: &[int], x: int) -> (index: int)
    requires(sorted(a))
    ensures(0 <= index < a.len() ==> a[index] == x)
    ensures(index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x)
{
}