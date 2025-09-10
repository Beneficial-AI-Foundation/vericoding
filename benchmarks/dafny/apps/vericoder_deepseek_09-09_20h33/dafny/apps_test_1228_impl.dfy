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
  ensures (n + a) % 4 == 1 ==> (n % 4 == 1 && a == 0) || (n % 4 == 0 && a == 1) || (n % 4 == 3 && a == 2)
  ensures (n + a) % 4 == 2 ==> (n % 4 == 2 && a == 0) || (n % 4 == 1 && a == 1) || (n % 4 == 0 && a == 2)
  ensures (n + a) % 4 == 3 ==> (n % 4 == 3 && a == 0) || (n % 4 == 2 && a == 1) || (n % 4 == 1 && a == 2)
{
  if a == 0 {
    assert n + a == n;
  } else if a == 1 {
    assert n + a == n + 1;
    if n % 4 == 0 {
      assert (n + 1) % 4 == 1;
    } else if n % 4 == 1 {
      assert (n + 1) % 4 == 2;
    } else if n % 4 == 2 {
      assert (n + 1) % 4 == 3;
    } else if n % 4 == 3 {
      assert (n + 1) % 4 == 0;
    }
  } else if a == 2 {
    assert n + a == n + 2;
    if n % 4 == 0 {
      assert (n + 2) % 4 == 2;
    } else if n % 4 == 1 {
      assert (n + 2) % 4 == 3;
    } else if n % 4 == 2 {
      assert (n + 2) % 4 == 0;
    } else if n % 4 == 3 {
      assert (n + 2) % 4 == 1;
    }
  }
}

lemma LemmaMod3Case(n: int, a: int)
  requires ValidInput(n)
  requires a == 2
  requires n % 4 == 3
  ensures (n + a) % 4 == 1
{
  // Explicit calculation for n % 4 == 3 and a == 2
  assert (n + 2) % 4 == (3 + 2) % 4 == 5 % 4 == 1;
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
    LemmaModArithmetic(n, a);
  } else if rem == 2 {
    a := 1;
    b := 'B';
    LemmaModArithmetic(n, a);
  } else if rem == 3 {
    a := 2;
    b := 'A';
    LemmaModArithmetic(n, a);
  } else {
    a := 1;
    b := 'A';
    LemmaModArithmetic(n, a);
  }
  assert OptimalChoice(n, a, b) by {
    assert b == GetCategory(n + a);
  }
}
// </vc-code>

