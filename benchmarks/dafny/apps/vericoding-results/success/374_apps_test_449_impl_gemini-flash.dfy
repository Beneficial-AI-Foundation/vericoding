// <vc-preamble>
predicate ValidInput(n: int) {
    n >= 1
}

function MinBills(n: int): int
    requires n >= 1
{
    n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
}
// </vc-preamble>

// <vc-helpers>
function GetBillCount(n: int, billValue: int): int
    requires n >= 0
    requires billValue > 0
{
    n / billValue
}

function GetRemainingAmount(n: int, billValue: int): int
    requires n >= 0
    requires billValue > 0
{
    n % billValue
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
  var n100 := GetBillCount(n, 100);  
  var rem100 := GetRemainingAmount(n, 100);

  var n20 := GetBillCount(rem100, 20);
  var rem20 := GetRemainingAmount(rem100, 20);

  var n10 := GetBillCount(rem20, 10);
  var rem10 := GetRemainingAmount(rem20, 10);

  var n5 := GetBillCount(rem10, 5);
  var rem5 := GetRemainingAmount(rem10, 5);

  var n1 := rem5;

  result := n100 + n20 + n10 + n5 + n1;
}
// </vc-code>
