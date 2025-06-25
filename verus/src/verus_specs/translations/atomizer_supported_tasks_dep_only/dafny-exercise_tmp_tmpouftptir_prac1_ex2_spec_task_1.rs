pub fn Deli(a: &mut [char], i: usize)
    requires(
        a.len() > 0,
        i < a.len(),
    )
    ensures(|result: ()| 
        forall|j: usize| 0 <= j < i ==> a[j] == old(a)[j] &&
        forall|j: usize| i <= j < a.len() - 1 ==> a[j] == old(a)[j + 1] &&
        a[a.len() - 1] == '.'
    )
{
}