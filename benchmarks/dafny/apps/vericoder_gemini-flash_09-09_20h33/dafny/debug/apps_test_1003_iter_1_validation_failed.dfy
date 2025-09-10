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
function method CeilingDivision(numerator: int, denominator: int): int
  requires denominator > 0
  ensures CeilingDivision(numerator, denominator) == (numerator + denominator - 1) / denominator
{
  (numerator + denominator - 1) / denominator
}

lemma lemma_SocksAfterDay_decreasing(n: int, m: int, day: int)
  requires m > 0
  decreases day
  ensures SocksAfterDay(n, m, day) >= SocksAfterDay(n, m, day + 1)
{
  calc {
    SocksAfterDay(n, m, day);
    n + day / m - day;
  }
  calc {
    SocksAfterDay(n, m, day + 1);
    n + (day + 1) / m - (day + 1);
  }
  // We need to show n + day / m - day >= n + (day + 1) / m - (day + 1)
  // This simplifies to day / m - day >= (day + 1) / m - (day + 1)
  // day / m - day >= (day + 1) / m - day - 1
  // day / m >= (day + 1) / m - 1
  // day / m + 1 >= (day + 1) / m
  // We know (day + 1) / m is either day / m or day / m + 1 if (day+1) is a multiple of m
  // So day / m + 1 >= (day + 1) / m holds.
  // Specifically, if day % m == m - 1, then (day+1)/m = day/m + 1. Otherwise (day+1)/m = day/m.
  // Case 1: day % m != m - 1 (or m = 1). Then (day + 1) / m == day / m.
  // In this case, day / m - day >= day / m - (day + 1)
  // -day >= -day - 1, which implies 0 >= -1, which is true.
  // Case 2: day % m == m - 1. Then (day + 1) / m == day / m + 1.
  // In this case, day / m - day >= (day / m + 1) - (day + 1)
  // day / m - day >= day / m + 1 - day - 1
  // day / m - day >= day / m - day, which means 0 >= 0, true.
}

lemma lemma_SocksAfterDay_monotonicity(n: int, m: int, k: int, delta: int)
  requires m > 0
  requires delta >= 0
  ensures SocksAfterDay(n, m, k) >= SocksAfterDay(n, m, k + delta)
{
  if delta == 0 {
    // Trivial
  } else {
    lemma_SocksAfterDay_decreasing(n, m, k);
    lemma_SocksAfterDay_monotonicity(n, m, k + 1, delta - 1);
  }
}

lemma lemma_SocksAfterDay_positive_before_zero(n: int, m: int, day: int)
  requires m > 0
  requires day >= 1
  requires SocksAfterDay(n, m, day) <= 0
  ensures SocksAfterDay(n, m, day - 1) > 0
  ensures forall k :: 1 <= k < day ==> SocksAfterDay(n, m, k) > 0
{
  // We know SocksAfterDay(n,m,day) <= 0.
  // We want to show SocksAfterDay(n,m,day-1) > 0.
  // Socks(n,m,d-1) = n + (d-1)/m - (d-1)
  // Socks(n,m,d)   = n + d/m - d
  // (d-1)/m - (d-1) - (d/m - d)
  // = (d-1-d)/m - (-1) when d-1 and d are in the same block wrt m, so (d-1)/m = d/m
  // In general: (d-1)/m - (d-1) - d/m + d = (d-1)/m - d/m + 1
  // (d-1)/m - d/m is either 0 or -1.
  // So Socks(n,m,d-1) - Socks(n,m,d) is either 1 or 0 (when d is multiple of m then (d-1)/m = d/m -1, then (d-1)/m-d/m = -1).
  // The difference is 1 if d is not a multiple of m, and 0 if d is a multiple of m. This is false logic.
  // Let's re-evaluate (d-1)/m - (d-1) compared to d/m - d.
  // Consider f(x) = x/m - x.
  // We have f(d-1) - f(d) = ((d-1)/m - (d-1)) - (d/m - d)
  // = (d-1)/m - d/m + 1
  // If d is a multiple of m, say d = km, then (d-1)/m = (km-1)/m = k-1.
  // So f(d-1) - f(d) = (k-1) - k + 1 = 0.
  // If d is not a multiple of m, then (d-1)/m = floor((d-1)/m) and d/m = floor(d/m).
  // Since d-1 and d are consecutive, floor((d-1)/m) and floor(d/m) are either equal or differ by 1.
  // They are equal if m does not divide d.
  // So if m does not divide d, then (d-1)/m = d/m.
  // Then f(d-1) - f(d) = d/m - d/m + 1 = 1.
  //
  // So, SocksAfterDay(n,m,day-1) = SocksAfterDay(n,m,day) + (1 or 0)
  // Specifically, SocksAfterDay(n,m,day-1) >= SocksAfterDay(n,m,day).
  // From lemma_SocksAfterDay_decreasing, we know SocksAfterDay(n,m,k) >= SocksAfterDay(n,m,k+1).
  // Thus, SocksAfterDay(n,m,day-1) >= SocksAfterDay(n,m,day).
  // If SocksAfterDay(n,m,day) <= 0:
  // If m does not divide day: SocksAfterDay(n,m,day-1) = SocksAfterDay(n,m,day) + 1. So SocksAfterDay(n,m,day-1) > 0 unless SocksAfterDay(n,m,day) = -1.
  // If m divides day: SocksAfterDay(n,m,day-1) = SocksAfterDay(n,m,day). This can lead to SocksAfterDay(n,m,day-1) <= 0.
  // This means if SocksAfterDay(n,m,day) <= 0, it's possible that SocksAfterDay(n,m,day-1) <= 0.
  // The lemma_SocksAfterDay_decreasing shows non-increasing nature.
  // We need to show that if day is the FIRST day such that SocksAfterDay(n,m,day) <= 0, then all previous days had > 0 socks.
  // The proof of this must be by induction or contradiction.

  // The core of the problem is finding the first 'day' where 'SocksAfterDay(n, m, day) <= 0'.
  // This is equivalent to finding the smallest 'day' such that n + day/m - day <= 0.
  // n <= day - day/m
  // n <= day * (1 - 1/m)
  // n <= day * (m-1)/m
  // day >= n * m / (m-1)
  // Since m >= 2, m-1 >= 1.
  // smallest integer day is CeilingDivision(n * m, m-1)
  // Let result = CeilingDivision(n * m, m-1).
  // Then for any k < result, k < n * m / (m-1).
  // k * (m-1)/m < n.
  // k + k/m < n. This is incorrect.
  // k * (m-1)/m < n implies k - k/m < n.
  // So n - (k - k/m) > 0.
  // n + k/m - k > 0. This is exactly SocksAfterDay(n,m,k) > 0.

  // The condition `requires day >= 1` and `requires SocksAfterDay(n, m, day) <= 0`
  // and `ensures SocksAfterDay(n, m, day - 1) > 0`
  // This specific lemma is proving that if day is the 'first' day, previous day is positive.
  // This is inherent in how we define `result`.
  // If result is the smallest integer such that SocksAfterDay(n, m, result) <= 0,
  // then for any k < result, SocksAfterDay(n, m, k) > 0 must hold.
  // So the proof for this lemma follows directly from the definition of the ceiling function applied
  // to the inequality.

  // The fact that the function is non-increasing (lemma_SocksAfterDay_monotonicity) is also important here.
  // If SocksAfterDay(n, m, day-1) <= 0, then by lemma_SocksAfterDay_monotonicity,
  // for any k < day-1, SocksAfterDay(n, m, k) <= SocksAfterDay(n,m,day-1) <= 0.
  // But we know that for k = 1, SocksAfterDay(n, m, 1) = n + 1/m - 1.
  // Since n >= 1, and m >= 2, 1/m - 1 is negative, but
  // 1/m - 1 >= 1/2 - 1 = -1/2.
  // So SocksAfterDay(n, m, 1) >= 1 - 1/2 = 1/2 > 0.
  // This means that SocksAfterDay(n, m, k) cannot be <= 0 for k=1.
  // Thus, there must be a first day 'result' such that SocksAfterDay(n, m, result) <= 0.
  // For this 'result', SocksAfterDay(n, m, result-1) must be > 0.

  // Proof by contradiction: Assume SocksAfterDay(n, m, day - 1) <= 0.
  // Since SocksAfterDay is non-increasing, if SocksAfterDay(n, m, day - 1) <= 0,
  // then for all k where 1 <= k <= day - 1, SocksAfterDay(n, m, k) <= SocksAfterDay(n, m, day - 1) <= 0.
  // But we know SocksAfterDay(n, m, 1) = n + 1/m - 1.
  // Since n >= 1, and m >= 2, then n + 1/m - 1 >= 1 + 1/2 - 1 = 1/2 > 0.
  // This contradicts `SocksAfterDay(n, m, 1) <= 0` (which would be true if day-1 >= 1 and SocksAfterDay(n,m,day-1) <= 0).
  // So our assumption `SocksAfterDay(n, m, day - 1) <= 0` must be false.
  // Therefore, SocksAfterDay(n, m, day - 1) > 0.

  // The second part of the ensures: forall k :: 1 <= k < day ==> SocksAfterDay(n, m, k) > 0.
  // This follows directly from the first part of the ensures and lemma_SocksAfterDay_monotonicity.
  // If we take any k such that 1 <= k < day, then k <= day - 1.
  // By lemma_SocksAfterDay_monotonicity, SocksAfterDay(n, m, k) >= SocksAfterDay(n, m, day - 1).
  // Since SocksAfterDay(n, m, day - 1) > 0, it means SocksAfterDay(n, m, k) > 0 for all such k.
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
    // We are looking for the smallest 'result' such that SocksAfterDay(n, m, result) <= 0.
    // SocksAfterDay(n, m, day) = n + day / m - day.
    // We want to find minimal 'day' such that n + day / m - day <= 0.
    // This is equivalent to n <= day - day / m.
    // Since day / m is floor(day / m), let's use the exact definition.
    // n <= day * (1 - 1/m) roughly, if m does not divide day, or day * (1 - 1/m) + something.
    // n <= day - (day - day % m) / m
    // n <= day - day/m, using integer division.
    // Let's rewrite the inequality: n + day/m <= day.
    // This is a bit tricky due to integer division.

    // Consider a binary search approach, or direct computation using the inverse function.
    // We know SocksAfterDay(n, m, 1) = n + 1/m - 1. Since n >= 1, m >= 2, 1/m - 1 >= 1/2 - 1 = -1/2.
    // So SocksAfterDay(n, m, 1) >= 1 - 1/2 = 1/2 > 0.
    // The function SocksAfterDay(n, m, day) is monotonically non-increasing (proven in lemma_SocksAfterDay_decreasing).
    // This means there will be a point where it transitions from positive to non-positive.
    // A linear search starting from 'n' (a lower bound given by `result >= n`)
    // or even '1' would also work since 'result' is bounded.
    // What is an upper bound for 'result'?
    // If SocksAfterDay(n, m, day) <= 0, then n + day/m - day <= 0.
    // n <= day - day/m.
    // Since day/m >= day/m - (m-1)/m, we have day - day/m <= day - (day/m - (m-1)/m) if day/m is a truncation.
    // day - day/m <= day - (day/m - 1).
    // The most negative value for SocksAfterDay is when day is very large.
    // SocksAfterDay(n, m, day) approx n + day/m - day = n - day*(m-1)/m.
    // So we need n - day*(m-1)/m <= 0.
    // n <= day*(m-1)/m.
    // day >= n * m / (m-1).
    // This suggests result is around n * m / (m-1).
    // Since m >= 2, m-1 >= 1.
    // If m = 2, result approx n * 2 / 1 = 2*n.
    // So an upper bound is maybe 2*n + some_constant.
    // Let's try `low = 1` and `high = 2*n + m` as search bounds.

    var low := 1;
    var high := 2 * n + m; // An upper bound; n*m/(m-1) is roughly 2n if m=2. Adding m accounts for ceiling and edge cases.
    result := high; // Initialize with a value that satisfies SocksAfterDay(n, m, result) <= 0 (eventually).

    // Binary search for the smallest `day` where `SocksAfterDay(n, m, day) <= 0`.
    // Loop invariant:
    // 1. ValidInput(n, m) (from precondition, immortal)
    // 2. 1 <= low <= high + 1
    // 3. (low == 1 || SocksAfterDay(n, m, low - 1) > 0)  // All days before 'low' are positive (or low is 1)
    // 4. (high >= 2*n || SocksAfterDay(n, m, high) <= 0) // 'high' is either an upper bound or a non-positive day
    // This loop invariant is a bit tricky for binary search.
    // A better invariant for finding the first true:
    // P(x) = (SocksAfterDay(n, m, x) <= 0)
    // We want to find smallest x such that P(x) is true.
    // Invariant: low <= high+1
    //            SocksAfterDay(n, m, low-1) > 0  (if low > 1)
    //            SocksAfterDay(n, m, high) <= 0 (if high is >= some 'true' value)
    //            The answer is in [low, high] or high+1.
    // When the loop terminates, low == high + 1, and low is the minimal 'day'.

    lemma_SocksAfterDay_monotonicity(n, m, low, high - low); // To prove SocksAfterDay(n,m,high) <= 0 is eventually true for a high enough value

    // The upper bound high = 2*n + m needs to be justified that SocksAfterDay(n,m,high) <= 0 for high = 2*n+m.
    // Consider n + day/m - day <= 0.
    // For day = 2*n+m, term day - day/m = day * (1 - 1/m) + (day%m)/m.
    // (2*n+m) - (2*n+m)/m = (2*n+m) - (2*n/m + 1). (assuming 2n is divisible by m for simplicity, or 2n/m uses floor).
    // (2*n+m) - (floor(2*n/m)+1).
    // We want n <= (2*n+m) - (floor(2*n/m)+1).
    // n <= 2*n + m - floor(2*n/m) - 1.
    // 0 <= n + m - floor(2*n/m) - 1.
    // This is true for n >= 1, m >= 2. floor(2n/m) >= 0. So n+m-1 >= 1+2-1 = 2.
    // This bound 'high' is sufficiently large that SocksAfterDay(n,m,high) <= 0 holds.
    // SocksAfterDay(n,m, high) = n + high/m - high <= n + (high/m) - high + (high%m)/m.
    // upper bound.
    // high >= n / (1 - 1/m) = n*m / (m-1)
    // Let (n*m + m - 2) / (m-1) be an explicit upper bound for the first day.
    // For n=1,m=2, result = 2. 1*2/(2-1) = 2.
    // For n=5,m=2, result = 10. 5*2/(2-1) = 10.
    // For n=5,m=3, result = ceiling(5*3/(3-1)) = ceiling(15/2) = 8.
    // SocksAfterDay(5,3,7) = 5 + 7/3 - 7 = 5 + 2 - 7 = 0. So 7 is result.
    // ceiling(15/2) = 8. Our upper bound 2*n+m = 10+3 = 13.
    // So the upper bound for the binary search should be the solution itself or slightly higher.

    // A more precise initial high value: n * m / (m - 1) + m
    // This is approx n * (1 + 1/(m-1)) + m.
    // For n=1, m=2, result should be 2. (1 * 2 / 1) + 2 = 4.
    // For n=1, m=10, result should be 1. (1 * 10 / 9) + 10 = 1 + 10 = 11.
    // (1 + 10/10 - 10) = 1 ok.
    // SocksAfterDay(1, 10, 1) = 1 + 1/10 - 1 = 0
    // SocksAfterDay(1, 10, 0) = 1 + 0 - 0 = 1 > 0
    // So for 1,10, result is 1.
    // So upper bound should be large enough to guarantee SocksAfterDay(n,m,high) is non-positive.
    // A simple `while (SocksAfterDay(n, m, high) > 0)` loop could find a good 'high' boundary.
    // Given n >= 1, m >= 2.
    // The result minimum value is 1 (e.g. n=1, m=2 -> SocksAfterDay(1,2,1) = 1+0-1=0).
    // The result maximum value:
    // If m-1=1 implies m=2. Then day >= n*2. So 2n.
    // So result is in [1, 2n+m].
    // low = 1, high = 2*n + m.

    // Invariant for binary search for smallest x satisfying P(x):
    // predicate P(x) { SocksAfterDay(n, m, x) <= 0 }
    // low <= x <= high+1 AND (low=1 OR !P(low-1)) AND P(high)
    // Here, P(low-1) means SocksAfterDay(n, m, low-1) <= 0. So !P(low-1) means SocksAfterDay(n, m, low-1) > 0.
    // Initial:
    // low = 1. SocksAfterDay(n,m,0) is not defined, so special check for low=1.
    // high = 2*n+m. We need to show that P(2*n+m) is true for a high enough bound.
    // As mentioned, n + day/m - day can be negative.
    // day - day/m value increases with day.
    // We want day - day/m >= n.
    // (m-1)/m * day <= day - day/m. (This lower bounds day - day/m, actual value is higher or equal)
    // We want (m-1)/m * day >= n. So day >= n*m/(m-1).
    // Our high value of 2*n+m is certainly >= n*m/(m-1) + any constant.
    // Proof:
    // 2n+m - n*m/(m-1) = (2n(m-1) + m(m-1) - nm) / (m-1)
    // = (2nm - 2n + m^2 - m - nm) / (m-1)
    // = (nm - 2n + m^2 - m) / (m-1)
    // = (n(m-2) + m(m-1)) / (m-1)
    // If m=2, this is (n(0) + 2(1))/1 = 2 >= 0.
    // If m>2, then m-2 >= 1, m-1 >= 1. numerator > 0. So high is sufficiently large.
    // Thus SocksAfterDay(n, m, high) <= 0 is true for high = 2*n+m and n>=1, m>=2.

    while (low <= high)
      invariant 1 <= low <= high + 1
      invariant (low == 1 || SocksAfterDay(n, m, low - 1) > 0)
      invariant SocksAfterDay(n, m, high) <= 0
      invariant forall k :: high < k && k <= 2*n + m ==> SocksAfterDay(n, m, k) <= 0
      invariant forall k :: 1 <= k < low ==> SocksAfterDay(n, m, k) > 0
    {
        var mid := low + (high - low) / 2;
        if (mid == 0) { // Should not happen if low >= 1
            mid := 1;
        }

        // We need to ensure that mid is a valid index, i.e., mid >= 1.
        // Since low >= 1, mid = low + (high-low)/2 will also be >= 1.

        if (SocksAfterDay(n, m, mid) <= 0) {
            // 'mid' could be the first day, or a day after the first.
            // We want the smallest day, so try smaller values.
            result := mid;
            high := mid - 1;
        } else {
            // SocksAfterDay(n, m, mid) > 0.
            // 'mid' is definitely not the first day.
            // The first day must be greater than 'mid'.
            low := mid + 1;
        }
    }
    // Loop terminates when low = high + 1.
    // At termination:
    // (low == 1 || SocksAfterDay(n, m, low - 1) > 0)
    // SocksAfterDay(n, m, high) <= 0
    // Result is the smallest value `k` such that `SocksAfterDay(n, m, k) <= 0`.
    // The `result` var stores the found minimum candidate.
    // When `SocksAfterDay(n, m, mid) <= 0`, we set `result = mid` and `high = mid - 1`.
    // This moves `high` to `mid - 1`, eventually making `high = low - 1`.
    // The final `result` will be `low` from the last step where `SocksAfterDay(n, m, mid) <= 0`.

    // The result from binary search will be 'result'.
    // `result` must be `low`.
    // If `result` is set on the last iteration where mid becomes `low`, then `result = low`.
    // Then `high` becomes `low - 1`, and the loop terminates.

    // Post-loop conditions:
    // `low = high + 1`
    // `SocksAfterDay(n, m, low - 1)` must have been positive (if low > 1) because if not, `low-1` would have become `result`
    // `SocksAfterDay(n, m, low)` must be non-positive because if it were positive, `low` would have been incremented.
    // Thus, `result = low` is the correct answer.

    // Final checks from ensures:
    // ensures result >= n:
    // SocksAfterDay(n, m, result) <= 0  ==> n + result/m - result <= 0 ==> n <= result - result/m.
    // If result = n, n <= n - n/m, which means n/m <= 0. Only possible if n=0, but n>=1.
    // So result cannot be n if m > 0.
    // However, consider SocksAfterDay(n, m, k) = n + k/m - k.
    // Note that m/(m-1) * n. If m=2, then 2n. So result >= 2n.
    // If result < n, then n + result/m - result > n + 1/m - n = 1/m > 0 for result=1.
    // What if result < n while being 1? e.g. n=2, m=2. result = 4. 4 >= 2.
    // For n=5, m=3, result = 7. 7 >= 5.
    // If result < n, then result/m - result < -n + result/m, less than 0.
    // SocksAfterDay(n,m,k) = n - k(1-1/m) approx n - k(m-1)/m.
    // If this is <=0, then n <= k(m-1)/m, so k >= n*m/(m-1).
    // Since m >= 2, m-1 >= 1.
    // m/(m-1) >= 2. So k >= 2*n.
    // Thus result >= 2*n.
    // Since n >= 1, 2*n >= n. So result >= n holds.

    // ensures result > 0: Result is found by binary search that starts with low=1, so result will be >= 1.

    // ensures SocksAfterDay(n, m, result) <= 0: This is direct from the loop's logic (assigned when `mid <= 0`).

    // ensures forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0:
    // This is also from the loop's invariant. Any 'mid' that yields 'SocksAfterDay(n, m, mid) > 0'
    // correctly increments low, preserving `forall k :: 1 <= k < low ==> SocksAfterDay(n, m, k) > 0`.
    // When loop finishes, `result` holds what `low` was.
    // So `forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0` holds.
    lemma_SocksAfterDay_positive_before_zero(n, m, result);
}
// </vc-code>

