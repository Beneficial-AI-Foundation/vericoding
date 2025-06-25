pub fn max(a: i32, b: i32) -> (c: i32)
    ensures(a >= b ==> c == a)
    ensures(b >= a ==> c == b)
{
}

pub fn max_test()
{
}