pub fn HasOnlyOneDistinctElement(a: &[i32]) -> (result: bool)
    ensures(result ==> forall|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j])
    ensures(!result ==> exists|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j])
{
}