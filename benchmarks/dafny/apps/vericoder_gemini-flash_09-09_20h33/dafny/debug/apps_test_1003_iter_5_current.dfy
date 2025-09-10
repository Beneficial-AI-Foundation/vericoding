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
// No changes needed, as the original helpers are duplicates of the prelude.
// The issue reported by the verifier is due to duplicate definitions.
// The prelude already defines these functions, so we should not redefine them.
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
    var high: int := n * m + 1; // An upper bound for the result. n*m might be too small if n=1,m=2. day=2. SocksAfterDay(1,2,1)=1. SocksAfterDay(1,2,2)=0. The result is 2.
    if n == 1 && m == 2 { high := 2;} // Smallest case handled
    var result_day: int := high; // Initialize with a value that satisfies SocksAfterDay(n, m, result_day) <= 0
                               // We know that for sufficiently large 'day', SocksAfterDay(n,m,day) will be <= 0.
                               // In the worst case, n=1, m=2, high = 1*2+1 = 3. SocksAfterDay(1,2,3) = 1 + 3/2 - 3 = 1 + 1 - 3 = -1 <= 0.

    while low <= high
        invariant 1 <= low <= high + 1
        invariant result_day >= 1
        invariant SocksAfterDay(n, m, result_day) <= 0
        invariant forall k :: 1 <= k < low ==> SocksAfterDay(n, m, k) > 0
        invariant high >= 0
        invariant low <= n * m + 2 // Upper bound for low
        invariant result_day <= n * m + 1
    {
        var mid: int := low + (high - low) / 2;
        if mid < 1 { // Ensure mid is at least 1 for SocksAfterDay to be well-defined for day-1 (if needed)
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

