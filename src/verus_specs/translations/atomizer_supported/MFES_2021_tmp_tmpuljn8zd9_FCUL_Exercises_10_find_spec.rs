pub fn find(a: &[i32], key: i32) -> (index: usize)
    requires(a.len() > 0)
    ensures(index <= a.len())
    ensures(index < a.len() ==> a[index] == key)
{
}