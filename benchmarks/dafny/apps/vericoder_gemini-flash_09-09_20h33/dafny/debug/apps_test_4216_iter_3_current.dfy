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
function MinFConsideredSoFar(N: int, limit: int): int
  requires N >= 1
  requires limit >= 1
  ensures MinFConsideredSoFar(N, limit) >= 1 // or a large value
{
  var currentMin := 2147483647; // Max int value
  var k := 1;
  while k < limit
    invariant 1 <= k <= limit
    invariant forall x :: 1 <= x < k && N % x == 0 ==> currentMin <= F(x, N / x)
    invariant forall x :: 1 <= x < k && N % x == 0 ==> currentMin <= F(N / x, x)
  {
    if N % k == 0 {
      var f1 := F(k, N / k);
      if f1 < currentMin then currentMin := f1;
      if k * k != N { // If k is not the square root, consider the symmetric pair
        var f2 := F(N / k, k);
        if f2 < currentMin then currentMin := f2;
      }
    }
    k := k + 1;
  }
  return currentMin;
}
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
    invariant min_f_value >= 1
    invariant forall a, b :: IsFactorPair(a, b, N) && a * a <= N ==> min_f_value <= F(a, b)
    invariant (exists a, b :: IsFactorPair(a, b, N) && a * a <= N && a < i) ==> min_f_value == MinFConsideredSoFar(N, i)
    invariant (forall a, b :: !IsFactorPair(a, b, N) || a * a > N || a >= i) ==> min_f_value == 2147483647
  {
    if N % i == 0 {
      var a := i;
      var b := N / i;
      var currentF := F(a, b);
      if currentF < min_f_value {
        min_f_value := currentF;
      }
      if a * a != N { // Check the symmetric pair (b, a) only if a != b
        currentF := F(b, a);
        if currentF < min_f_value {
          min_f_value := currentF;
        }
      }
    }
    i := i + 1;
  }
  result := min_f_value;
}
// </vc-code>

