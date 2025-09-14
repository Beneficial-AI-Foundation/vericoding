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
  var hundreds := n / 100;
  var rem100 := n % 100;
  var twenties := rem100 / 20;
  var rem20 := rem100 % 20;
  var tens := rem20 / 10;
  var rem10 := rem20 % 10;
  var fives := rem10 / 5;
  var ones := rem10 % 5;
  result := hundreds + twenties + tens + fives + ones;
}
// </vc-code>

