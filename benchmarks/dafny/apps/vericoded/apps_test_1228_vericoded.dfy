function GetCategory(hp: int): char
{
    var remainder := hp % 4;
    if remainder == 1 then 'A'
    else if remainder == 3 then 'B'
    else if remainder == 2 then 'C'
    else 'D'
}

predicate ValidInput(n: int)
{
    30 <= n <= 100
}

predicate ValidOutput(a: int, b: char)
{
    0 <= a <= 2 && (b == 'A' || b == 'B' || b == 'C' || b == 'D')
}

predicate OptimalChoice(n: int, a: int, b: char)
{
    b == GetCategory(n + a) &&
    ((n % 4 == 1) ==> (a == 0 && b == 'A')) &&
    ((n % 4 == 2) ==> (a == 1 && b == 'B')) &&
    ((n % 4 == 3) ==> (a == 2 && b == 'A')) &&
    ((n % 4 == 0) ==> (a == 1 && b == 'A'))
}

// <vc-helpers>
lemma GetCategoryProperties(hp: int)
    ensures hp % 4 == 1 ==> GetCategory(hp) == 'A'
    ensures hp % 4 == 3 ==> GetCategory(hp) == 'B'
    ensures hp % 4 == 2 ==> GetCategory(hp) == 'C'
    ensures hp % 4 == 0 ==> GetCategory(hp) == 'D'
{
    var remainder := hp % 4;
}

lemma ModuloAddition(n: int, k: int)
    ensures (n + k) % 4 == ((n % 4) + k) % 4
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (a: int, b: char)
    requires ValidInput(n)
    ensures ValidOutput(a, b)
    ensures OptimalChoice(n, a, b)
    ensures b == 'A' || b == 'B'
// </vc-spec>
// <vc-code>
{
    var remainder := n % 4;
    
    if remainder == 1 {
        a := 0;
        b := 'A';
        GetCategoryProperties(n);
    } else if remainder == 2 {
        a := 1;
        b := 'B';
        ModuloAddition(n, 1);
        assert (n + 1) % 4 == 3;
        GetCategoryProperties(n + 1);
    } else if remainder == 3 {
        a := 2;
        b := 'A';
        ModuloAddition(n, 2);
        assert (n + 2) % 4 == 1;
        GetCategoryProperties(n + 2);
    } else {
        assert remainder == 0;
        a := 1;
        b := 'A';
        ModuloAddition(n, 1);
        assert (n + 1) % 4 == 1;
        GetCategoryProperties(n + 1);
    }
}
// </vc-code>

