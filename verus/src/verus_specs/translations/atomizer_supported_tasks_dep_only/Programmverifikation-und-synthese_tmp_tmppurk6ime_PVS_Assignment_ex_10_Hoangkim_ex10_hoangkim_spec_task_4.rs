pub fn q(x: nat, y: nat) -> (z: nat)
    requires(y - x > 2)
    ensures(x < z * z < y)
{
}

pub fn strange()
    ensures(1 == 2)
{
}