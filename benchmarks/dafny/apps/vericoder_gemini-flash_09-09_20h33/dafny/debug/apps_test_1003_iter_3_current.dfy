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
    var result_day: int := high; // Initialize with a value that satisfies SocksAfterDay(n, m, result_day) <= 0
                               // We know that for sufficiently large 'day', SocksAfterDay(n,m,day) will be <= 0.
                               // In the worst case, n=1, m=2, high = 1*2 = 2. SocksAfterDay(1,2,2) = 1 + 2/2 - 2 = 1 + 1 - 2 = 0 <= 0.

    while low <= high
        invariant 1 <= low <= high + 1
        invariant 1 <= result_day <= n * m // result_day is always within a reasonable range
        invariant SocksAfterDay(n, m, result_day) <= 0
        invariant forall k :: 1 <= k < low ==> SocksAfterDay(n, m, k) > 0
        invariant high >= low - 1
    {
        var mid: int := low + (high - low) / 2;
        if mid == 0 { // Ensure mid is at least 1 for the loop invariant
          low := 1;
          continue;
        }

        if SocksAfterDay(n, m, mid) > 0 {
            low := mid + 1;
        } else {
            result_day := mid;
            high := mid - 1;
        }
    }
    return result_day;
}
// </vc-code>

