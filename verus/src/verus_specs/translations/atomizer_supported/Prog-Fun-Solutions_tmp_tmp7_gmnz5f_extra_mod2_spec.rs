spec fn f2(n: nat) -> nat {
    if n == 0 { 0 } else { 5 * f2(n / 3) + n % 4 }
}

pub fn mod2(n: nat) -> (a: nat)
    ensures a == f2(n)
{
}