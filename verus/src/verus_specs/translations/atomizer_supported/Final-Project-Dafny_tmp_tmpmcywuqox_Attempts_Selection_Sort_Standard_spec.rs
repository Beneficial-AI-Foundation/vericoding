pub fn selection_sorted(array: &mut Vec<i32>)
    requires(true)
    ensures(multiset(old(array)) == multiset(array))
{
}