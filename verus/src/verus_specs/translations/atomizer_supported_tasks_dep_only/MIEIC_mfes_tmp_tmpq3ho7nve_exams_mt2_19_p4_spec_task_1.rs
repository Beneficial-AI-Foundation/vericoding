spec fn R(n: nat) -> nat {
    if n == 0 { 0 } else if R((n-1) as nat) > n { R((n-1) as nat) - n } else { R((n-1) as nat) + n }
}

pub fn calcR(n: nat) -> (r: nat)
    ensures r == R(n)
{
}