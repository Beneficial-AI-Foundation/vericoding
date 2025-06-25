pub fn LinearSearch3<T: PartialEq>(data: &[T], Element: T, s1: &[T]) -> (position: i32)
    requires(
        s1.len() <= data.len(),
        forall|i: usize| 0 <= i && i < s1.len() ==> s1[i] == data[data.len() - 1 - i]
    )
    ensures(|position: i32|
        (position == -1 || position >= 1) &&
        (position >= 1 ==> exists|i: usize| 0 <= i && i < s1.len() && s1[i] == Element && s1.len() != 0)
    )
{
}