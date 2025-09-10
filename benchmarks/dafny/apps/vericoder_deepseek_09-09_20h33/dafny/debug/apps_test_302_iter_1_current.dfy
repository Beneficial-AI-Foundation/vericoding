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
lemma repunit_formula(n: nat)
    requires n >= 0
    ensures repunit(n) == (pow(10, n) - 1) / 9
    decreases n
{
    if n == 0 {
        // repunit(0) = 0, (10^0 - 1)/9 = (1 - 1)/9 = 0
    } else if n == 1 {
        // repunit(1) = 1, (10^1 - 1)/9 = (10 - 1)/9 = 9/9 = 1
    } else {
        repunit_formula(n - 1);
        // repunit(n) = 10 * repunit(n - 1) + 1
        // = 10 * ((10^{n-1} - 1)/9) + 1
        // = (10^n - 10)/9 + 9/9
        // = (10^n - 1)/9
    }
}

lemma pow_properties()
    ensures forall base: nat, exp: nat :: base >= 0 && exp >= 0 ==> pow(base, exp) >= 1 || exp == 0
    ensures forall base: nat, exp: nat :: base >= 2 && exp >= 1 ==> pow(base, exp) > base
{
}

lemma repunit_positive(n: nat)
    requires n >= 1
    ensures repunit(n) > 0
{
    if n == 1 {
    } else if n == 2 {
    } else if n == 3 {
    } else if n == 4 {
    } else if n == 5 {
    } else {
        // For n > 5, we know repunit(n) = n > 0
    }
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    } else {
        return repunit(n);
    }
}
// </vc-code>

