spec fn sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

pub fn BinarySearch(a: &[i32], x: i32) -> (index: i32)
    requires sorted(a)
    ensures 0 <= index < a.len() ==> a[index as int] == x
    ensures index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x
{
}