pub fn pal_verify(a: &[char]) -> (yn: bool)
    ensures(yn == true ==> forall|i: usize| 0 <= i < a.len()/2 ==> a[i] == a[a.len() - i - 1])
    ensures(yn == false ==> exists|i: usize| 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1])
    ensures(forall|j: usize| 0 <= j < a.len() ==> a[j] == old(a)[j])
{
}