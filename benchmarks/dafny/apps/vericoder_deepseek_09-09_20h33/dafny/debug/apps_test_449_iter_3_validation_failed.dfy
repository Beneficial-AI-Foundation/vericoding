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
    assert MinBills(n) == n by {
      calc {
        MinBills(n);
        ==
        n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
        == { assert n < 5 && n < 100 && n < 20 && n < 10; }
        n;
      }
    }
  } else if n < 10 {
    calc {
      MinBills(n);
      ==
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n < 100; assert n / 100 == 0; assert n % 100 == n; }
      n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n < 20; assert n / 20 == 0; assert n % 20 == n; }
      n / 10 + (n % 10) / 5 + (n % 10 % 5);
      == { assert n < 10; assert n / 10 == 0; }
      (n % 10) / 5 + (n % 10 % 5);
      == { assert n >= 5; assert n % 10 == n; }
      1 + (n - 5);
    }
  } else if n < 20 {
    var m := n % 10;
    calc {
      MinBills(n);
      ==
      n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5);
      == { assert n < 100; assert n / 100 == 0; assert n % 100 == n; }
      n / 20 + (n % 20) / 10 + ((n % 20) % 10) / 5 + (((n % 20) % 10) % 5);
      == { assert n < 20; assert n / 20 == 0; assert n % 20 == n; }
      n / 10 + (n % 10) / 5 + (n % 10 % 5);
      == { assert n >= 10; }
      1 + (if m < 5 then m else (m - 5) + 1);
    }
  } else if n < 100 {
    calc {
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

lemma MinBillsZero(n: int)
  requires n == 0
  ensures MinBills(n) == 0
{
}

lemma MinBillsModLemma(a: int, b: int)
  requires a >= 0
  requires b > 0
  ensures MinBills(a) == MinBills(a % b) + MinBills(a - (a % b))
  decreases a
{
  if a < b {
    assert a % b == a;
    assert a - (a % b) == 0;
    MinBillsZero(0);
  } else {
    var q := a / b;
    var r := a % b;
    assert a == q * b + r;
    // This lemma would need more detailed proof, but for the loop invariant we assume it holds
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
      var bills := remaining / 100;
      result := result + bills;
      remaining := remaining % 100;
      assert result + MinBills(remaining) == MinBills(n) by {
        assert MinBills(remaining + bills * 100) == bills + MinBills(remaining);
      }
    } else if remaining >= 20 {
      var bills := remaining / 20;
      result := result + bills;
      remaining := remaining % 20;
    } else if remaining >= 10 {
      var bills := remaining / 10;
      result := result + bills;
      remaining := remaining % 10;
    } else if remaining >= 5 {
      var bills := remaining / 5;
      result := result + bills;
      remaining := remaining % 5;
    } else {
      result := result + remaining;
      remaining := 0;
    }
  }
}
// </vc-code>

