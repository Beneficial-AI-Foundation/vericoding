pub fn busca<T>(a: &[T], x: T) -> (r: i32)
where
    T: PartialEq,
    requires(true),
    ensures(|r: i32| 0 <= r ==> r < a.len() && a[r as usize] == x),
    ensures(|r: i32| r < 0 ==> forall|i: usize| 0 <= i < a.len() ==> a[i] != x),
{
}