spec fn f(n: nat) -> nat {
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

pub fn mod(n: nat) -> (a: nat)
    ensures(a == f(n))
{
}