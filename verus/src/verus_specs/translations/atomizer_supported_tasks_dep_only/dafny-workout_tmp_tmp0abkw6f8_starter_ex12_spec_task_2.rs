pub fn find_max(a: &[i32]) -> usize
    requires(a.len() > 0)
    ensures(|max_idx: usize| 0 <= max_idx < a.len())
    ensures(|max_idx: usize| forall|j: usize| 0 <= j < a.len() ==> a[max_idx] >= a[j])
{
}

pub fn main()
{
}