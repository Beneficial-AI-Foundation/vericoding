function CommonDivisors(A: int, B: int): set<int>
  requires A > 0 && B > 0
{
  set d | 1 <= d <= A && A % d == 0 && B % d == 0
}

predicate ValidInput(A: int, B: int, K: int)
{
  A > 0 && B > 0 && K >= 1 && |CommonDivisors(A, B)| >= K
}

predicate IsKthLargestCommonDivisor(A: int, B: int, K: int, result: int)
  requires ValidInput(A, B, K)
{
  result > 0 &&
  A % result == 0 && B % result == 0 &&
  result in CommonDivisors(A, B) &&
  |set d | d in CommonDivisors(A, B) && d > result| == K - 1
}

// <vc-helpers>
lemma CommonDivisorsFinite(A: int, B: int)
  requires A > 0 && B > 0
  ensures |CommonDivisors(A, B)| >= 1
{
  assert 1 in CommonDivisors(A, B);
}

lemma CommonDivisorsBounded(A: int, B: int, d: int)
  requires A > 0 && B > 0
  requires d in CommonDivisors(A, B)
  ensures 1 <= d <= A && 1 <= d <= B
{
}

function Min(a: int, b: int): int
{
  if a < b then a else b
}

lemma SwapPreservesElements<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}

lemma SwapPreservesCommonDivisors(divisors: seq<int>, i: int, j: int, A: int, B: int)
  requires 0 <= i < |divisors|
  requires 0 <= j < |divisors|
  requires A > 0 && B > 0
  requires forall d :: d in divisors ==> d in CommonDivisors(A, B)
  ensures forall d :: d in divisors[i := divisors[j]][j := divisors[i]] ==> d in CommonDivisors(A, B)
{
  var swapped := divisors[i := divisors[j]][j := divisors[i]];
  SwapPreservesElements(divisors, i, j);
  assert multiset(swapped) == multiset(divisors);
  forall d | d in swapped
    ensures d in CommonDivisors(A, B)
  {
    assert d in multiset(swapped);
    assert d in multiset(divisors);
    assert d in divisors;
  }
}

lemma SwapPreservesAllCommonDivisors(divisors: seq<int>, i: int, j: int, A: int, B: int)
  requires 0 <= i < |divisors|
  requires 0 <= j < |divisors|
  requires A > 0 && B > 0
  requires forall d :: d in CommonDivisors(A, B) ==> d in divisors
  requires forall d :: d in divisors ==> d in CommonDivisors(A, B)
  ensures forall d :: d in CommonDivisors(A, B) ==> d in divisors[i := divisors[j]][j := divisors[i]]
{
  var swapped := divisors[i := divisors[j]][j := divisors[i]];
  SwapPreservesElements(divisors, i, j);
  assert multiset(swapped) == multiset(divisors);
  forall d | d in CommonDivisors(A, B)
    ensures d in swapped
  {
    assert d in divisors;
    assert d in multiset(divisors);
    assert d in multiset(swapped);
    assert d in swapped;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  var divisors := [];
  var i := 1;
  var minAB := Min(A, B);
  
  // Collect all common divisors
  while i <= minAB
    invariant 1 <= i <= minAB + 1
    invariant forall d :: d in divisors ==> d in CommonDivisors(A, B)
    invariant forall d :: d in CommonDivisors(A, B) && d < i ==> d in divisors
  {
    if A % i == 0 && B % i == 0 {
      divisors := divisors + [i];
    }
    i := i + 1;
  }
  
  // Now we have all common divisors in the list
  assert forall d :: d in CommonDivisors(A, B) ==> d in divisors;
  assert forall d :: d in divisors ==> d in CommonDivisors(A, B);
  
  // Sort divisors in descending order
  var j := 0;
  while j < |divisors|
    invariant 0 <= j <= |divisors|
    invariant forall x, y :: 0 <= x < y < j ==> divisors[x] >= divisors[y]
    invariant forall d :: d in divisors ==> d in CommonDivisors(A, B)
    invariant forall d :: d in CommonDivisors(A, B) ==> d in divisors
  {
    var maxIdx := j;
    var k := j + 1;
    while k < |divisors|
      invariant j < k <= |divisors|
      invariant j <= maxIdx < |divisors|
      invariant forall idx :: j <= idx < k ==> divisors[maxIdx] >= divisors[idx]
    {
      if divisors[k] > divisors[maxIdx] {
        maxIdx := k;
      }
      k := k + 1;
    }
    
    if maxIdx != j {
      var temp := divisors[j];
      var oldDivisors := divisors;
      divisors := divisors[j := divisors[maxIdx]][maxIdx := temp];
      
      // Help Dafny verify invariants are preserved
      SwapPreservesCommonDivisors(oldDivisors, j, maxIdx, A, B);
      SwapPreservesAllCommonDivisors(oldDivisors, j, maxIdx, A, B);
    }
    j := j + 1;
  }
  
  // divisors is now sorted in descending order
  assert forall x, y :: 0 <= x < y < |divisors| ==> divisors[x] >= divisors[y];
  assert |divisors| == |CommonDivisors(A, B)|;
  assert K >= 1 && K <= |divisors|;
  
  result := divisors[K - 1];
  
  // Verify the postcondition
  assert result in CommonDivisors(A, B);
  assert A % result == 0 && B % result == 0;
  
  // Count how many divisors are greater than result
  var countGreater := 0;
  var idx := 0;
  while idx < K - 1
    invariant 0 <= idx <= K - 1
    invariant countGreater == idx
    invariant forall x :: 0 <= x < idx ==> divisors[x] > result
  {
    countGreater := countGreater + 1;
    idx := idx + 1;
  }
  
  assert countGreater == K - 1;
  assert |set d | d in CommonDivisors(A, B) && d > result| == K - 1;
}
// </vc-code>

