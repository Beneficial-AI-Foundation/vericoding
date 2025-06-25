pub fn LinearSearch<T>(a: &[T], P: impl Fn(T) -> bool) -> (n: i32)
    ensures(
        -1 <= n < a.len(),
        n == -1 || P(a[n as usize]),
        n != -1 ==> forall|i: usize| 0 <= i < n ==> !P(a[i]),
        n == -1 ==> forall|i: usize| 0 <= i < a.len() ==> !P(a[i])
    )
{
}

pub fn LinearSearch1<T>(a: &[T], P: impl Fn(T) -> bool, s1: Seq<T>) -> (n: i32)
    requires(
        s1.len() <= a.len(),
        forall|i: usize| 0 <= i < s1.len() ==> s1[i] == a[i]
    )
    ensures(
        -1 <= n < a.len(),
        n == -1 || P(a[n as usize]),
        n != -1 ==> forall|i: usize| 0 <= i < n ==> !P(a[i]),
        n == -1 ==> forall|i: usize| 0 <= i < s1.len() ==> !P(a[i])
    )
{
}

pub fn LinearSearch2<T>(data: &[T], Element: T, s1: Seq<T>) -> (position: i32)
    requires(
        s1.len() <= data.len(),
        forall|i: usize| 0 <= i < s1.len() ==> s1[i] == data[i]
    )
    ensures(
        position == -1 || position >= 1,
        position >= 1 ==> exists|i: usize| 0 <= i < s1.len() && s1[i] == Element,
        position == -1 ==> forall|i: usize| 0 <= i < s1.len() ==> s1[i] != Element
    )
{
}

pub fn LinearSearch3<T>(data: &[T], Element: T, s1: Seq<T>) -> (position: i32)
    requires(
        s1.len() <= data.len(),
        forall|i: usize| 0 <= i < s1.len() ==> s1[i] == data[data.len() - 1 - i]
    )
    ensures(
        position == -1 || position >= 1,
        position >= 1 ==> exists|i: usize| 0 <= i < s1.len() && s1[i] == Element && s1.len() != 0
    )
{
}