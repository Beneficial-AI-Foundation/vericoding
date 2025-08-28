ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
lemma f_property(n: nat)
    ensures f(n) >= 1
{
    if n == 0 {
    } else if n % 2 == 0 {
        f_property(n/2);
    } else {
        f_property(n/2);
    }
}

function power2(n: nat): nat
{
    if n == 0 then 1 else 2 * power2(n - 1)
}

lemma power2_positive(n: nat)
    ensures power2(n) > 0
{
    if n == 0 {
    } else {
        power2_positive(n - 1);
    }
}

lemma mod_correctness(n: nat, result: nat, temp: nat, i: nat)
    requires power2(i) > 0
    requires temp == n / power2(i)
    requires result == if temp == 0 then 1 else (if temp % 2 == 0 then 1 + 2 * f(temp / 2) else 2 * f(temp / 2))
    ensures result == f(n / power2(i))
{
    power2_positive(i);
    if temp == 0 {
        assert n / power2(i) == 0;
        assert f(0) == 1;
    } else if temp % 2 == 0 {
        assert f(temp) == 1 + 2 * f(temp / 2);
    } else {
        assert f(temp) == 2 * f(temp / 2);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        return 1;
    }
    
    a := mod_helper(n);
}

method mod_helper(n: nat) returns (result: nat)
    ensures result == f(n)
    decreases n
{
    if n == 0 {
        result := 1;
    } else if n % 2 == 0 {
        var half_result := mod_helper(n / 2);
        result := 1 + 2 * half_result;
    } else {
        var half_result := mod_helper(n / 2);
        result := 2 * half_result;
    }
}
// </vc-code>
