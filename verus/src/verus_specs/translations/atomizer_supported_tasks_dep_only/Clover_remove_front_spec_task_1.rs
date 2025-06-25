pub fn remove_front(a: &[i32]) -> (c: Vec<i32>)
    requires(a.len() > 0)
    ensures(a.subrange(1, a.len() as int) =~= c@)
{
}