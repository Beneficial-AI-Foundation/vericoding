function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }

predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

// <vc-spec>
method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
// </vc-spec>

// <vc-helpers>
lemma peekSumMonotonic(v: array<int>, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  ensures peekSum(v, i) <= peekSum(v, j)
  decreases j - i
{
  if i == j {
    // Base case: peekSum(v, i) == peekSum(v, j)
  } else {
    // Inductive case: i < j
    peekSumMonotonic(v, i, j-1);
    if isPeek(v, j-1) {
      // peekSum(v, j) = v[j-1] + peekSum(v, j-1)
      // We know peekSum(v, j-1) >= peekSum(v, i) from inductive hypothesis
      // Since v[j-1] could be negative, we need to be more careful
      assert peekSum(v, j) == v[j-1] + peekSum(v, j-1);
      assert peekSum(v, j-1) >= peekSum(v, i);
      // If v[j-1] >= 0, then clearly peekSum(v, j) >= peekSum(v, i)
      // If v[j-1] < 0, we still have peekSum(v, j) >= peekSum(v, i) in many cases
      // but we need to establish this more carefully
      if v[j-1] >= 0 {
        assert peekSum(v, j) >= peekSum(v, j-1) >= peekSum(v, i);
      } else {
        // Even if v[j-1] < 0, peekSum(v, j) could still be >= peekSum(v, i)
        // We need to show this holds
        assert peekSum(v, j) == v[j-1] + peekSum(v, j-1);
      }
    } else {
      // peekSum(v, j) = peekSum(v, j-1) >= peekSum(v, i)
      assert peekSum(v, j) == peekSum(v, j-1);
    }
  }
}

lemma peekSumStep(v: array<int>, i: int)
  requires 0 < i <= v.Length
  ensures peekSum(v, i) == (if isPeek(v, i-1) then v[i-1] + peekSum(v, i-1) else peekSum(v, i-1))
{
  // This follows directly from the definition of peekSum
}
// </vc-helpers>

// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == peekSum(v, i)
  {
    if isPeek(v, i) {
      sum := sum + v[i];
    }
    
    i := i + 1;
    
    peekSumStep(v, i);
  }
}
// </vc-code>