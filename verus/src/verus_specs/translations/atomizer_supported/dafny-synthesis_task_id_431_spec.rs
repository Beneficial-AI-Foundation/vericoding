pub fn HasCommonElement(a: &[i32], b: &[i32]) -> (result: bool)
    requires(
        true
    )
    ensures(|result: bool|
        result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i as usize] == b[j as usize]
    )
    ensures(|result: bool|
        !result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i as usize] != b[j as usize]
    )
{
}