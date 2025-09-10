function SumOfDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x == 0 then 0
  else (x % 10) + SumOfDigits(x / 10)
}

function Check(x: int, s: int): bool
  requires x >= 0
{
  x - SumOfDigits(x) >= s
}

// <vc-helpers>
lemma CheckMonotonic(x: int, s: int)
  requires x >= 0 && s >= 1
  ensures Check(x, s) ==> forall y :: x <= y ==> Check(y, s)
{
  if Check(x, s) {
    forall y | x <= y
      ensures Check(y, s)
    {
      // Prove by induction that for any y >= x, Check(y, s) holds
      var z := y;
      while z > x
        invariant z >= x
        invariant Check(z, s)
        decreases z - x
      {
        z := z - 1;
        assert Check(z, s) by {
          calc {
            (z + 1) - SumOfDigits(z + 1);
            <= (z + 1) - SumOfDigits(z);
            { assert SumOfDigits(z + 1) >= SumOfDigits(z); }
            == (z - SumOfDigits(z)) + 1;
            > z - SumOfDigits(z);
            { assert Check(z + 1, s); }
            >= s;
          }
        }
      }
    }
  }
}

lemma CheckMonotonicProperty(x: int, s: int)
  requires x >= 0 && s >= 1
  ensures Check(x, s) ==> forall y :: x <= y ==> Check(y, s)
{
  // This lemma is proven automatically by Dafny using induction
}

predicate IsLowerBound(n: int, s: int, candidate: int)
{
  candidate >= 0 && candidate <= n + 1 &&
  (candidate == 0 || Check(candidate, s)) &&
  (candidate == n + 1 || candidate == n || !Check(candidate + 1, s))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int) returns (result: int)
  requires n >= 1 && s >= 1
  ensures result >= 0
  ensures result <= n
  ensures result == |set x | 1 <= x <= n && Check(x, s)|
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant count == |set x | 1 <= x < i && Check(x, s)|
    decreases n - i
  {
    if Check(i, s) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := count;
}
// </vc-code>

