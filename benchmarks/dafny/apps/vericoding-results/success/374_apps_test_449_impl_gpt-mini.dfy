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
  var b100 := n / 100;
  var b20 := (n % 100) / 20;
  var b10 := ((n % 100) % 20) / 10;
  var b5 := (((n % 100) % 20) % 10) / 5;
  var b1 := ((((n % 100) % 20) % 10) % 5);
  result := b100 + b20 + b10 + b5 + b1;
}
// </vc-code>

