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
    else if n < 20 then (n - 10) / 5 + 1 + if n % 10 < 5 then n % 10 else (n % 10 - 5) + 1
    else if n < 100 then (n - 20) / 10 + 2 + MinBills(n % 20)
    else n / 100 + MinBills(n % 100)
{
  if n < 5 {
  } else if n < 10 {
    calc {
      MinBills(n);
      == { assert n % 100 == n; assert n % 20 == n; assert n % 10 == n; }
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n / 100 == 0; }
      (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n % 100 == n; }
      n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n >= 5 && n < 10; assert n / 20 == 0; assert n % 20 == n; }
      (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n % 20 == n; }
      n / 10 + (n % 10) / 5 + (n % 10 % 5);
      == { assert n < 10; assert n / 10 == 0; }
      (n % 10) / 5 + (n % 10 % 5);
      == { assert n >= 5; assert n % 10 >= 5; }
      (n - 5) + 1;
    }
  } else if n < 20 {
  } else if n < 100 {
    calc <= {
      MinBills(n);
      ==
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n < 100; assert n / 100 == 0; assert n % 100 == n; }
      n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      ==
      (n - 20) / 10 + 2 + MinBills(n % 20);
    }
  } else {
    calc {
      MinBills(n);
      ==
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      ==
      n / 100 + MinBills(n % 100);
    }
  }
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
    if remaining >= 100 {
      result := result + remaining / 100;
      remaining := remaining % 100;
    } else if remaining >= 20 {
      result := result + remaining / 20;
      remaining := remaining % 20;
    } else if remaining >= 10 {
      result := result + remaining / 10;
      remaining := remaining % 10;
    } else if remaining >= 5 {
      result := result + remaining / 5;
      remaining := remaining % 5;
    } else {
      result := result + remaining;
      remaining := 0;
    }
  }
}
// </vc-code>

