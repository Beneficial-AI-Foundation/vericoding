pub fn m2(x: nat) -> (y: int)
    requires(x <= -1)
    ensures(|y: int| y > x && y < x)
{
}