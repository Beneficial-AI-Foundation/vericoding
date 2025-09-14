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
  var r := n % 4;
  if r == 1 {
    a := 0;
    b := GetCategory(n + a);
    var q := n / 4;
    assert n == 4 * q + 1;
    assert n + a == 4 * q + 1;
    assert (n + a) % 4 == 1;
    assert b == 'A';
  } else if r == 2 {
    a := 1;
    b := GetCategory(n + a);
    var q := n / 4;
    assert n == 4 * q + 2;
    assert n + a == 4 * q + 3;
    assert (n + a) % 4 == 3;
    assert b == 'B';
  } else if r == 3 {
    a := 2;
    b := GetCategory(n + a);
    var q := n / 4;
    assert n == 4 * q + 3;
    assert n + a == 4 * (q + 1) + 1;
    assert (n + a) % 4 == 1;
    assert b == 'A';
  } else {
    assert r == 0;
    a := 1;
    b := GetCategory(n + a);
    var q := n / 4;
    assert n == 4 * q + 0;
    assert n + a == 4 * q + 1;
    assert (n + a) % 4 == 1;
    assert b == 'A';
  }
}
// </vc-code>

