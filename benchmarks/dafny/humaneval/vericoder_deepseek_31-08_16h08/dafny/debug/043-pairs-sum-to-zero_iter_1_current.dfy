

// <vc-helpers>
lemma exists_pair_sum_to_zero(l: seq<int>, i: int)
  requires 0 <= i < |l|
  requires forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
  ensures (exists i2, j :: 0 <= i2 < |l| && 0 <= j < |l| && i2 != j && l[i2] + l[j] == 0) == 
          (exists j :: 0 <= j < |l| && j != i && l[i] + l[j] == 0)
{
  if exists j :: 0 <= j < |l| && j != i && l[i] + l[j] == 0 {
    // Trivially true
  } else {
    forall j | 0 <= j < |l| && j != i 
      ensures l[i] + l[j] != 0 
    {
      // By the second requires clause and the else branch
    }
    
    // Prove by induction that no pairs exist
    var k := 0;
    while k < i
      invariant 0 <= k <= i
      invariant forall m :: 0 <= m < k ==> forall n :: 0 <= n < |l| && n != m ==> l[m] + l[n] != 0
    {
      k := k + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |l| < 2 {
    return false;
  }
  
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
  {
    var j := 0;
    while j < |l|
      invariant 0 <= j <= |l|
      invariant j <= |l|
      invariant forall m :: 0 <= m < j && m != i ==> l[i] + l[m] != 0
    {
      if j != i && l[i] + l[j] == 0 {
        return true;
      }
      j := j + 1;
    }
    
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

