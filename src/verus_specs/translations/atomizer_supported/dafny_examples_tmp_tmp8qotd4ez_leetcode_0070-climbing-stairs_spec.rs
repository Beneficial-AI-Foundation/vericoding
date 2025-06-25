spec fn stairs(n: nat) -> nat {
    if n <= 1 { 1 } else { stairs(n - 2) + stairs(n - 1) }
}

pub fn climb_stairs(n: usize) -> (r: usize)
    requires n >= 0,
    ensures r == stairs(n as nat),
{
}