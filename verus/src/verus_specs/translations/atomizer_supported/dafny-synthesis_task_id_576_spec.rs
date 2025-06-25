pub fn is_sublist(sub: Vec<i32>, main: Vec<i32>) -> (result: bool)
    ensures(
        true == exists|i: usize| 0 <= i && i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len())
    )
{
}