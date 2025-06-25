pub fn IsEven(a: int) -> bool
    requires(a >= 0)
{
}

pub fn EvenSquare(a: int)
    requires(a >= 0)
    ensures(IsEven(a) ==> IsEven(a * a))
{
}

pub fn EvenDouble(a: int)
    requires(a >= 0)
    ensures(IsEven(a + a))
{
}

pub fn EvenPlus(x: int, y: int)
    requires(x >= 0)
    requires(y >= 0)
    requires(IsEven(x))
    requires(IsEven(y))
    ensures(IsEven(x + y))
{
}

pub fn EvenTimes(x: int, y: int)
    requires(x >= 0)
    requires(y >= 0)
    requires(IsEven(x))
    requires(IsEven(y))
    ensures(IsEven(x * y))
{
}