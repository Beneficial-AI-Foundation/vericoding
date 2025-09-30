ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
lemma f_step(n: nat)
    requires n > 0
    ensures n % 2 == 0 ==> f(n) == 1 + 2 * f(n/2)
    ensures n % 2 == 1 ==> f(n) == 2 * f(n/2)
{
    if n % 2 == 0 {
        calc == {
            f(n);
            1 + 2 * f(n/2);
        }
    } else {
        calc == {
            f(n);
            2 * f(n/2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// <vc-code>
{
    var m := n;
    var acc := 0;
    var power := 1;
    
    while m > 0
        invariant 0 <= m <= n
        invariant f(n) == acc + power * f(m)
        decreases m
    {
        if m % 2 == 0 {
            // When m is even: f(m) = 1 + 2*f(m/2)
            // So power * f(m) = power * (1 + 2*f(m/2)) = power + 2*power*f(m/2)
            // We add power to acc and update power to 2*power
            f_step(m);
            assert f(m) == 1 + 2 * f(m/2);
            assert power * f(m) == power * (1 + 2 * f(m/2));
            assert power * f(m) == power + 2 * power * f(m/2);
            acc := acc + power;
        } else {
            // When m is odd: f(m) = 2*f(m/2)
            // So power * f(m) = power * 2 * f(m/2) = 2*power*f(m/2)
            f_step(m);
            assert f(m) == 2 * f(m/2);
            assert power * f(m) == 2 * power * f(m/2);
        }
        power := power * 2;
        m := m / 2;
    }
    
    assert m == 0;
    assert f(0) == 1;
    a := acc + power;
}
// </vc-code>

