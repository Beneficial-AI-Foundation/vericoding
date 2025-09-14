ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
lemma f_positive(n: nat)
ensures f(n) > 0
{
    if n == 0 {
    } else if n % 2 == 0 {
        f_positive(n/2);
    } else {
        f_positive(n/2);
    }
}

lemma f_even_decomp(n: nat)
requires n > 0 && n % 2 == 0
ensures f(n) == 1 + 2 * f(n/2)
{
}

lemma f_odd_decomp(n: nat) 
requires n > 0 && n % 2 == 1
ensures f(n) == 2 * f(n/2)
{
}

lemma f_bounds(n: nat)
ensures f(n) >= 1
{
    f_positive(n);
}
// </vc-helpers>

// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1;
    }
    
    var result := 0;
    var current := n;
    var power := 1;
    
    while current > 0
    invariant current >= 0
    invariant result + power * f(current) == f(n)
    invariant power > 0
    invariant result >= 0
    decreases current
    {
        if current % 2 == 0 {
            result := result + power;
            power := power * 2;
            current := current / 2;
        } else {
            power := power * 2;
            current := current / 2;
        }
    }
    
    // When current == 0, we have result + power * f(0) == f(n)
    // Since f(0) == 1, we have result + power == f(n)
    result := result + power;
    
    return result;
}
// </vc-code>

