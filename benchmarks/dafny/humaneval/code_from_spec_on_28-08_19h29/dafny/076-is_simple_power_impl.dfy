function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
function Power(base: nat, exp: nat): nat {
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

ghost predicate IsPower(x: int, n: int, exp: nat) {
    if exp == 0 then x == 1
    else if n == 0 then x == 0
    else x == Power(n as nat, exp)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_simple_power(x: int, n: int) -> bool
Your task is to write a function that returns true if a number x is a simple power of n and false in other cases. x is a simple power of n if n**int=x
*/
// </vc-description>

// <vc-spec>
method is_simple_power(x: int, n: int) returns (result: bool)
    requires n >= 0
    ensures result == exists k: nat :: (n == 0 ==> x == 0) && Power(n as nat, k) == x
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return x == 0;
    }
    if x == 1 {
        return true;
    }
    if x <= 0 {
        return false;
    }
    var current := 1;
    while current < x
        invariant current > 0
        invariant exists k: nat :: Power(n as nat, k) == current
        decreases x - current
    {
        if current > x / n {
            return false;
        }
        current := current * n;
    }
    return current == x;
}
// </vc-code>
