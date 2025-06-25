pub fn LinearSearch2<T>(data: &[T], Element: T, s1: &[T]) -> (position: i32)
where
    T: std::cmp::PartialEq,
requires(
    s1.len() <= data.len(),
    forall|i: usize| 0 <= i && i < s1.len() ==> s1[i] == data[i],
)
ensures(|position: i32|
    position == -1 || position >= 1,
    position >= 1 ==> exists|i: usize| 0 <= i && i < s1.len() && s1[i] == Element,
    position == -1 ==> forall|i: usize| 0 <= i && i < s1.len() ==> s1[i] != Element,
)
{
}