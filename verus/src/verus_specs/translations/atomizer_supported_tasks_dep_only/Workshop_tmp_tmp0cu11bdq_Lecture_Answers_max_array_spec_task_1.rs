pub fn max(a: &[int]) -> (max: int)
    requires(a.len() > 0)
    ensures(|max: int| forall|j: usize| j < a.len() ==> max >= a[j])
    ensures(|max: int| exists|j: usize| j < a.len() && max == a[j])
{
}