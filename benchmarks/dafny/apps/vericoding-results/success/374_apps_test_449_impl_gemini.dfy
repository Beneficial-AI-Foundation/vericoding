predicate ValidInput(n: int) {
    n >= 1
}

function MinBills(n: int): int
    requires n >= 1
{
    n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 0
    ensures result == MinBills(n)
// </vc-spec>
// <vc-code>
{
  var remaining := n;
  result := 0;
  
  result := result + remaining / 100;
  remaining := remaining % 100;
  
  result := result + remaining / 20;
  remaining := remaining % 20;
  
  result := result + remaining / 10;
  remaining := remaining % 10;
  
  result := result + remaining / 5;
  remaining := remaining % 5;
  
  result := result + remaining;
}
// </vc-code>

