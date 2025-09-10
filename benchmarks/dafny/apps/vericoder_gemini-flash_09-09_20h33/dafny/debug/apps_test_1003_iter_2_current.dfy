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
function method SocksAfterDay(n: int, m: int, day: int): int
  requires m > 0
{
    n + day / m - day
}

predicate method CanWearSocksOnDay(n: int, m: int, day: int)
  requires m > 0
{
    day >= 1 ==> SocksAfterDay(n, m, day - 1) > 0
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
    var low: int := 1;
    var high: int := n * m; // An upper bound for the result
    var result: int := 0;

    while low <= high
        invariant 1 <= low <= high + 1
        invariant result >= 0
        invariant (result == 0 || SocksAfterDay(n, m, result) <= 0)
        invariant (low == 1 || forall k :: 1 <= k < low ==> SocksAfterDay(n, m, k) > 0)
        invariant high >= low - 1
    {
        var mid: int := low + (high - low) / 2;
        if SocksAfterDay(n, m, mid) > 0 {
            low := mid + 1;
        } else {
            result := mid;
            high := mid - 1;
        }
    }
    return result;
}
// </vc-code>

