// <vc-preamble>
function Power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else if exp == 1 then base
  else base * Power(base, exp - 1)
}

predicate ValidInput(D: int, N: int)
{
  0 <= D <= 2 && 1 <= N <= 100
}

predicate DivisibleExactlyDTimes(num: int, D: int)
  requires 0 <= D <= 2
{
  if D == 0 then 
    num > 0 && num % 100 != 0
  else 
    num > 0 && 
    num % Power(100, D) == 0 && 
    num % Power(100, D + 1) != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(D: int, N: int) returns (result: int)
  requires ValidInput(D, N)
  ensures DivisibleExactlyDTimes(result, D)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  if D == 0 {
    // Find N-th number not divisible by 100
    var count := 0;
    var current := 1;
    while count < N
      invariant 0 <= count <= N
      invariant current >= 1
      decreases N - count
    {
      if current % 100 != 0 {
        count := count + 1;
        if count == N {
          result := current;
          return;
        }
      }
      current := current + 1;
    }
    result := 1; // fallback, should not be reached
  } else if D == 1 {
    // Find N-th number divisible by 100 but not by 10000
    // The N-th such number is N*100 if N*100 is not divisible by 10000
    // Otherwise, we need to skip multiples of 10000
    var candidate := N * 100;
    if candidate % 10000 != 0 {
      result := candidate;
    } else {
      // If N*100 is divisible by 10000, we need to find the next valid number
      // We know that (N*100 + 100) will work since adding 100 won't make it divisible by 10000
      result := candidate + 100;
    }
  } else {
    // D == 2: Find N-th number divisible by 10000 but not by 1000000
    // The N-th such number is N*10000 if N*10000 is not divisible by 1000000
    // Otherwise, we need to skip multiples of 1000000
    var candidate := N * 10000;
    if candidate % 1000000 != 0 {
      result := candidate;
    } else {
      // If N*10000 is divisible by 1000000, we need to find the next valid number
      // We know that (N*10000 + 10000) will work since adding 10000 won't make it divisible by 1000000
      result := candidate + 10000;
    }
  }
}
// </vc-code>
