spec fn potencia(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        x * potencia(x, y - 1)
    }
}

pub fn pot(x: nat, y: nat) -> (r: nat)
    ensures r == potencia(x, y)
{
}