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
lemma LemmaModArithmetic(n: int, a: int)
  requires ValidInput(n)
  requires 0 <= a <= 2
  ensures (n + a) % 4 == 0 ==> n % 4 == (4 - a % 4) % 4
  ensures (n + a) % 4 == 1 ==> (n % 4 == 1 && a == 0) || (n % 4 == 0 && a == 1)
  ensures (n + a) % 4 == 2 ==> (n % 4 == 2 && a == 0) || (n % 4 == 1 && a == 1) || (n % 4 == 0 && a == 2)
  ensures (n + a) % 4 == 3 ==> (n % 4 == 3 && a == 0) || (n % 4 == 2 && a == 1) || (n % 4 == 1 && a == 2)
{
  // This lemma helps reason about the relationship between n and a mod 4
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
  var rem := n % 4;
  if rem == 1 {
    a := 0;
    b := 'A';
  } else if rem == 2 {
    a := 1;
    b := 'B';
  } else if rem == 3 {
    a := 2;
    b := 'A';
  } else {
    a := 1;
    b := 'A';
  }
}
// </vc-code>

