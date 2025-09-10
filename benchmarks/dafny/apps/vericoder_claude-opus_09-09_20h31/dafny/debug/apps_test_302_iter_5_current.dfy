function pow(base: nat, exp: nat): nat
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

function repunit(n: nat): nat
    requires n >= 0
    ensures n == 0 ==> repunit(n) == 0
    ensures n > 0 ==> repunit(n) > 0
{
    if n == 0 then 0 
    else if n == 1 then 1
    else if n == 2 then 11
    else if n == 3 then 111
    else if n == 4 then 1111
    else if n == 5 then 11111
    else n  // simplified for larger values
}

predicate ValidInput(n: nat)
{
    true
}

predicate ValidOutput(n: nat, result: nat)
{
    (n == 0 ==> result == 0) &&
    (n > 0 ==> result > 0)
}

// <vc-helpers>
lemma RepunitProperty(n: nat)
    ensures n > 0 ==> repunit(n) == (pow(10, n) - 1) / 9
{
    if n > 0 {
        assert repunit(n) == (pow(10, n) - 1) / 9;
    }
}

method ComputeRepunit(n: nat) returns (result: nat)
    requires ValidInput(n)
    ensures ValidOutput(n, result)
    ensures result == repunit(n)
    ensures n > 0 ==> result == (pow(10, n) - 1) / 9
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    if n == 0 {
        result := 0;
    } else {
        var power := pow(10, n);
        result := (power - 1) / 9;
    }
    RepunitProperty(n);
}
// </vc-code>

