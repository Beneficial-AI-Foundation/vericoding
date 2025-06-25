pub fn Max(x: nat, y: nat) -> (r: nat)
    ensures(r >= x && r >= y)
    ensures(r == x || r == y)
{
}