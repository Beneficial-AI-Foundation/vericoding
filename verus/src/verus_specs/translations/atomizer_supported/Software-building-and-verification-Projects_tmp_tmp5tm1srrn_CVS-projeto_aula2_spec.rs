pub fn max(a: int, b: int) -> z: int
    requires(true)
    ensures(z >= a || z >= b)
{
}

pub fn Main()
{
}

pub fn mystery1(n: nat, m: nat) -> res: nat
    ensures(n + m == res)
{
}

pub fn mystery2(n: nat, m: nat) -> res: nat
    ensures(n * m == res)
{
}

pub fn m1(x: int, y: int) -> z: int
    requires(0 < x < y)
    ensures(z >= 0 && z < y && z != x)
{
}

pub fn m2(x: nat) -> y: int
    requires(x <= -1)
    ensures(y > x && y < x)
{
}

pub fn m3(x: int, y: int) -> z: bool
    ensures(z ==> x == y)
{
}

pub fn m4(x: int, y: int) -> z: bool
    ensures(z ==> x == y && x == y ==> z)
{
}