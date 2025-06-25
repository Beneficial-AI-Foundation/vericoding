pub fn pal_verify(a: &[char]) -> (yn: bool)
    requires(true)
    ensures(|result: bool| yn == true ==> (forall|i: usize| 0 <= i < a.len()/2 ==> a[i] == a[a.len() - i - 1]))
    ensures(|result: bool| yn == false ==> (exists|i: usize| 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1]))
    ensures(|result: bool| forall|j: usize| 0 <= j < a.len() ==> a[j] == old(a)[j])
{
}

pub fn test()
    requires(true)
    ensures(true)
{
}