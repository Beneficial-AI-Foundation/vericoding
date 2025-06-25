pub fn m1(x: int, y: int) -> (z: int)
    requires(0 < x < y)
    ensures(|z: int| z >= 0 && z <= y && z != x)
{
}