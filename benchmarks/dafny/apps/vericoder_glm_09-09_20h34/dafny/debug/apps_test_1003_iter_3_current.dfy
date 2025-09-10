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
lemma Lemma_SocksAfterDay_Monotonic(n: int, m: int, d1: int, d2: int)
  requires m > 0
  requires d1 <= d2
  ensures SocksAfterDay(n, m, d1) >= SocksAfterDay(n, m, d2)
{
  calc {
    SocksAfterDay(n, m, d1);
    n + d1 / m - d1;
    n + d1 / m - d1 + (d2 - d1) / m - (d2 - d1) - ((d2 - d1) / m - (d2 - d1));
    { assert (d2 - d1) / m - (d2 - d1) <= 0; }
    n + (d1 + (d2 - d1)) / m - (d1 + (d2 - d1)) + ((d2 - d1) - (d2 - d1) / m);
    n + d2 / m - d2 + (d2 - d1) * (m - 1) / m;
    >= n + d2 / m - d2;
    SocksAfterDay(n, m, d2);
  }
}

lemma Lemma_SocksAfterDay_BaseCase(n: int, m: int)
  requires ValidInput(n, m)
  ensures SocksAfterDay(n, m, 0) == n
{
  calc {
    SocksAfterDay(n, m, 0);
    n + 0 / m - 0;
    n;
  }
}

lemma Lemma_SocksAfterDay_Decrease(n: int, m: int, day: int)
  requires m > 0
  requires SocksAfterDay(n, m, day) > 0
  ensures SocksAfterDay(n, m, day + 1) < SocksAfterDay(n, m, day)
{
  calc {
    SocksAfterDay(n, m, day + 1);
    n + (day + 1) / m - (day + 1);
    n + day / m - day + ((day + 1) % m == 0 ? 1 : 0) - 1;
    SocksAfterDay(n, m, day) + ((day + 1) % m == 0 ? 1 : 0) - 1;
    <= SocksAfterDay(n, m, day) + 1 - 1;
    SocksAfterDay(n, m, day);
  }
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
  var day := 0;
  
  Lemma_SocksAfterDay_BaseCase(n, m);
  
  while SocksAfterDay(n, m, day) > 0
    invariant 0 <= day
    invariant forall k :: 0 <= k < day ==> SocksAfterDay(n, m, k) > 0
  {
    day := day + 1;
    Lemma_SocksAfterDay_Decrease(n, m, day - 1);
  }
  
  result := day;
}
// </vc-code>

