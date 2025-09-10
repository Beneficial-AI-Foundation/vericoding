predicate ValidInput(n: int) {
    n >= 1
}

function MinBills(n: int): int
    requires n >= 1
{
    n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
}

// <vc-helpers>
lemma MinBillsFormula(n: int)
  requires n >= 1
  ensures MinBills(n) == 
    if n < 5 then n
    else if n < 10 then (n - 5) + 1
    else if n < 20 then (n - 10) / 5 + 1 + (if n % 10 < 5 then n % 10 else (n % 10 - 5) + 1)
    else if n < 100 then (n - 20) / 10 + 2 + MinBills(n % 20)
    else n / 100 + MinBills(n % 100)
{
  if n < 5 {
    calc == {
      MinBills(n);
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n % 100 == n; assert n % 20 == n; assert n % 10 == n; }
      n / 100 + n / 20 + n / 10 + n / 5 + n % 5;
      == { assert n < 5; assert n / 100 == 0; assert n / 20 == 0; assert n / 10 == 0; assert n / 5 == 0; }
      n % 5;
      n;
    }
  } else if n < 10 {
    calc == {
      MinBills(n);
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n % 100 == n; }
      n / 100 + n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n < 10; assert n / 100 == 0; assert n / 20 == 0; assert n % 20 == n; }
      n / 10 + (n % 10) / 5 + (n % 10 % 5);
      == { assert n >= 5 && n < 10; assert n / 10 == 0; assert n % 10 >= 5; }
      1 + (n - 5);
      (n - 5) + 1;
    }
  } else if n < 20 {
    var k := n % 10;
    calc == {
      MinBills(n);
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n % 100 == n; }
      n / 100 + n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n < 20; assert n / 100 == 0; assert n / 20 == 0; assert n % 20 == n; }
      n / 10 + (n % 10) / 5 + (n % 10 % 5);
      == { assert n >= 10; }
      1 + (if k < 5 then k else (k - 5) + 1);
      (n - 10) / 5 + 1 + (if k < 5 then k else (k - 5) + 1);
    }
  } else if n < 100 {
    calc == {
      MinBills(n);
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n < 100; assert n / 100 == 0; assert n % 100 == n; }
      n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n % 20 >= 1 || n % 20 == 0; if n % 20 != 0 { assert n % 20 >= 1; } }
      n / 20 + MinBills(n % 20);
      == { assert n / 20 == (n - 20) / 10 + 2; }
      (n - 20) / 10 + 2 + MinBills(n % 20);
    }
  } else {
    calc == {
      MinBills(n);
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      n / 100 + MinBills(n % 100);
    }
  }
}

lemma MinBillsRecursive(n: int)
  requires n >= 1
  ensures MinBills(n) ==
    if n >= 100 then n / 100 + MinBills(n % 100)
    else if n >= 20 then n / 20 + MinBills(n % 20)
    else if n >= 10 then n / 10 + MinBills(n % 10)
    else if n >= 5 then n / 5 + MinBills(n % 5)
    else n
{
  MinBillsFormula(n);
  if n >= 100 {
    assert n % 100 >= 1 || n % 100 == 0;
  } else if n >= 20 {
    MinBillsFormula(n);
    assert n % 20 >= 1 || n % 20 == 0;
  } else if n >= 10 {
    MinBillsFormula(n);
    assert n % 10 >= 1 || n % 10 == 0;
  } else if n >= 5 {
    MinBillsFormula(n);
    assert n % 5 >= 1 || n % 5 == 0;
  }
}

lemma ModNonNegative(n: int, d: int)
  requires d > 0
  ensures n % d >= 0
{
}

lemma ModLessThanDivisor(n: int, d: int)
  requires d > 0
  ensures n % d < d
{
}

lemma ModZeroOrPositive(n: int, d: int)
  requires d > 0
  ensures n % d == 0 || n % d >= 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 0
    ensures result == MinBills(n)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var remaining := n;
  
  while remaining > 0
    invariant remaining >= 0
    invariant result + MinBills(remaining) == MinBills(n)
  {
    MinBillsRecursive(remaining);
    if remaining >= 100 {
      result := result + remaining / 100;
      remaining := remaining % 100;
      ModZeroOrPositive(remaining, 100);
      assert remaining == 0 || remaining >= 1;
    } else if remaining >= 20 {
      result := result + remaining / 20;
      remaining := remaining % 20;
      ModZeroOrPositive(remaining, 20);
      assert remaining == 0 || remaining >= 1;
    } else if remaining >= 10 {
      result := result + remaining / 10;
      remaining := remaining % 10;
      ModZeroOrPositive(remaining, 10);
      assert remaining == 0 || remaining >= 1;
    } else if remaining >= 5 {
      result := result + remaining / 5;
      remaining := remaining % 5;
      ModZeroOrPositive(remaining, 5);
      assert remaining == 0 || remaining >= 1;
    } else {
      result := result + remaining;
      remaining := 0;
    }
  }
}
// </vc-code>

