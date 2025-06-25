pub fn find(a: &[i32], key: i32) -> (index: i32)
    ensures(
        -1 <= index < a.len(),
        index != -1 ==> a[index as int] == key && forall|i: int| 0 <= i < index ==> a[i] != key,
        index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
    )
{
}