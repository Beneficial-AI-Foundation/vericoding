ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>
lemma f2_recursion_helper(n: nat)
    requires n > 0
    ensures f2(n) == 5*f2(n/3) + n%4
{
    // This follows directly from the definition of f2
}

lemma f2_base_case()
    ensures f2(0) == 0
{
    // This follows directly from the definition of f2
}
// </vc-helpers>

// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        a := 0;
    } else {
        var sub_result := mod2(n/3);
        a := 5 * sub_result + n % 4;
    }
}
// </vc-code>

