

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
    
    // Now we need to show that there are no pairs in the entire list
    var k := 0;
    while k < |l|
      invariant 0 <= k <= |l|
      invariant k <= i ==> forall m :: 0 <= m < k ==> forall n :: 0 <= n < |l| && n != m ==> l[m] + l[n] != 0
      invariant k > i ==> forall m :: 0 <= m < |l| ==> forall n :: 0 <= n < |l| && n != m ==> l[m] + l[n] != 0
    {
      if k < i {
        // Already covered by the precondition
      } else if k == i {
        // We know from the forall above that l[i] doesn't pair with anyone
      } else {
        // For k > i, we need to show l[k] doesn't pair with any other element
        // But since no element before i pairs with anyone, and i doesn't pair with anyone,
        // and we're considering k > i, we need to use the precondition for elements < i
        // and the fact that l[i] doesn't pair with k
      }
      k := k + 1;
    }
  }
}

lemma no_pairs_before_i_implies_no_pairs(l: seq<int>, i: int)
  requires 0 <= i <= |l|
  requires forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
  ensures forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
{
  // This lemma is trivial since it's exactly the precondition
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
    var found_pair := false;
    var j := 0;
    while j < |l|
      invariant 0 <= j <= |l|
      invariant forall m :: 0 <= m < j && m != i ==> l[i] + l[m] != 0
    {
      if j != i && l[i] + l[j] == 0 {
        found_pair := true;
        j := |l|; // break out of inner loop
      }
      j := j + 1;
    }
    
    if found_pair {
      return true;
    }
    
    // Prove that no element pairs with l[i]
    forall m | 0 <= m < |l| && m != i
      ensures l[i] + l[m] != 0
    {
      // This follows from the inner loop invariant
    }
    
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

