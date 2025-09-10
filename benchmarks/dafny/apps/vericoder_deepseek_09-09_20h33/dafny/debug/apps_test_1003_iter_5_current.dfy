predicate ValidInput(n: int, m: int) {
    n >= 1 && m >= 2
}

function SocksAfterDay(n: int, m: int, day: int): int
  requires m > 0
{
    n + day / m - day
}

predicate CanWearSocksOnDay(n: int, m: int, day: int) 
  requires m > 0
{
    day >= 1 ==> SocksAfterDay(n, m, day - 1) > 0
}

// <vc-helpers>
lemma LemmaSocksAfterDayDecreasing(n: int, m: int, day: int)
  requires m > 0
  requires day >= 0
  ensures SocksAfterDay(n, m, day + 1) < SocksAfterDay(n, m, day)
{
}

lemma LemmaSocksAfterDayDecreasingByOne(n: int, m: int, day: int)
  requires m > 0
  requires day >= 0
  ensures SocksAfterDay(n, m, day + 1) == SocksAfterDay(n, m, day) - 1
  || (SocksAfterDay(n, m, day) <= m && SocksAfterDay(n, m, day + 1) == SocksAfterDay(n, m, day) - 1 + m)
{
}

function FindLastPositiveDay(n: int, m: int): int
  requires ValidInput(n, m)
  ensures result >= n
  ensures result > 0
  ensures SocksAfterDay(n, m, result) <= 0
  ensures forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0
{
  var day := n;
  while SocksAfterDay(n, m, day) > 0
    invariant day >= n
    invariant SocksAfterDay(n, m, day) >= -1
    invariant forall k :: 1 <= k < day ==> SocksAfterDay(n, m, k) > 0
  {
    day := day + 1;
  }
  day
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= n
  ensures result > 0
  ensures SocksAfterDay(n, m, result) <= 0
  ensures forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0
// </vc-spec>
// <vc-code>
{
  result := n;
  
  while SocksAfterDay(n, m, result) > 0
    invariant result >= n
    invariant SocksAfterDay(n, m, result) >= -1
    invariant forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0
  {
    result := result + 1;
  }
}
// </vc-code>

