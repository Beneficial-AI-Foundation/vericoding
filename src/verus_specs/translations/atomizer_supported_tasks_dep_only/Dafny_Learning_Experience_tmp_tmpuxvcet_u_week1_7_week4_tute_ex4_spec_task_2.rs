pub fn LinearSearch1<T>(a: &[T], P: impl Fn(T) -> bool, s1: Seq<T>) -> (n: i32)
    requires
        s1.len() <= a.len(),
        forall|i: int| 0 <= i < s1.len() ==> s1[i] == a[i],
    ensures |n: i32|
        -1 <= n < a.len(),
        n == -1 || P(a[n as int]),
        n != -1 ==> forall|i: int| 0 <= i < n ==> !P(a[i]),
        n == -1 ==> forall|i: int| 0 <= i < s1.len() ==> !P(a[i]),
{
}