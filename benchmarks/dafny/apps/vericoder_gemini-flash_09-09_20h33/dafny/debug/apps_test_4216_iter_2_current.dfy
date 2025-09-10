function numDigits(n: int): int
  requires n >= 1
  ensures numDigits(n) >= 1
  decreases n
{
  if n < 10 then 1
  else 1 + numDigits(n / 10)
}

predicate ValidInput(N: int) {
  N >= 1
}

function F(a: int, b: int): int
  requires a >= 1 && b >= 1
{
  var digitsA := numDigits(a);
  var digitsB := numDigits(b);
  if digitsA > digitsB then digitsA else digitsB
}

predicate IsFactorPair(a: int, b: int, N: int) {
  a >= 1 && b >= 1 && a * b == N
}

// <vc-helpers>
// The duplicate function F in helpers should be removed or renamed if it's meant to be a helper.
// Given that a function F is already defined in the preamble and used in the spec/code,
// this helper F is redundant and causes a duplicate member name error.
// The functions `numDigits` and `IsFactorPair` from the preamble are sufficient for verification context.
// No specific helper function is needed here, as F is already defined as a top-level function.
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures result >= 1
  ensures exists a, b :: IsFactorPair(a, b, N) && result == F(a, b)
  ensures forall a, b :: IsFactorPair(a, b, N) ==> result <= F(a, b)
// </vc-spec>
// <vc-code>
{
  var min_f_value := 2147483647; // A sufficiently large initial value
  var i := 1;
  while i * i <= N
    invariant i >= 1
    invariant N >= 1
    invariant (exists a, b :: IsFactorPair(a, b, N)) ==> min_f_value >= 1
    invariant forall a, b :: IsFactorPair(a, b, N) && a < i ==> min_f_value <= F(a, b)
    invariant min_f_value == (if exists a, b :: IsFactorPair(a, b, N) && a < i then (MinFConsideredSoFar(N, i) by {
        if i == 1 && min_f_value == 2147483647 then
            // When i is 1, no factor pair has been processed yet that satisfies a < i.
            // So if `min_f_value` hasn't changed, it means no factors were processed yet.
            // The constraint is about `a < i`, which means when i=1, no such 'a' exists.
            // The actual factors are processed when N % i == 0.
            // If factors are processed, min_f_value holds the min for those factors.
            // The empty set minimum is considered to be infinity, which 2147483647 represents.
            // If no factor has been found yet:
            calc {
                min_f_value;
                2147483647;
            }
        else if i > 1 && (exists a, b :: IsFactorPair(a, b, N) && a < i) then
             // This is the inductive step. min_f_value should reflect the minimum F for factors a < i
             // that have been checked so far (i.e., those for which N % j == 0 for j < i).
             // The values of a are `j` where `j < i` and `N % j == 0`.
             if exists k :: k < i && N % k == 0 then
                 min_f_value == (MinFConsideredSoFar(N, i) by {
                     var currentMin := 2147483647;
                     var current_k := 1;
                     while current_k < i
                         invariant 1 <= current_k <= i
                         invariant forall x :: x < current_k && N % x == 0 ==> currentMin <= F(x, N/x)
                         invariant forall x :: x < current_k && N % x == 0 ==> currentMin <= F(N/x, x)
                         {
                            if N % current_k == 0 {
                                if F(current_k, N/current_k) < currentMin then currentMin := F(current_k, N/current_k);
                                if N/current_k != current_k && F(N/current_k, current_k) < currentMin then currentMin := F(N/current_k, current_k);
                            }
                            current_k := current_k + 1;
                         }
                     calc { min_f_value; currentMin; }
                 })
             else
                 min_f_value == 2147483647 // No factors found yet
        else
            min_f_value == 2147483647
    }) else min_f_value == 2147483647) // If no pair satisfies IsFactorPair(a, b, N) and a < i
  {
    if N % i == 0 {
      var a := i;
      var b := N / i;
      var currentF := F(a, b);
      if currentF < min_f_value {
        min_f_value := currentF;
      }
      if a != b { // Check the symmetric pair (b, a) only if a != b
        currentF := F(b, a);
        if currentF < min_f_value {
          min_f_value := currentF;
        }
      }
    }
    i := i + 1;
  }
  result := min_f_value;
  return result;
}
// </vc-code>

