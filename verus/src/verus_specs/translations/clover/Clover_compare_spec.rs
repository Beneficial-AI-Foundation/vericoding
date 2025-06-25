pub fn Compare<T: Eq>(a: T, b: T) -> (eq: bool)
    ensures(
        a == b ==> eq == true,
        a != b ==> eq == false,
    )
{
}