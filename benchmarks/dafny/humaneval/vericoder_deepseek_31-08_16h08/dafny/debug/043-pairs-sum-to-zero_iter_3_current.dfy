

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
    // Show that l[i] doesn't pair with any other element
    forall j | 0 <= j < |l| && j != i 
      ensures l[i] + l[j] != 0 
    {
      // By the else branch assumption
    }
    
    // Now show there are no pairs at all
    var k := 0;
    while k < |l|
      invariant 0 <= k <= |l|
      invariant forall m :: 0 <= m < k ==> forall n :: 0 <= n < |l| && n != m ==> l[m] + l[n] != 0
    {
      if k < i {
        // Already covered by precondition
      } else {
        // For k >= i, we need to show l[k] doesn't pair with any other element
        forall n | 0 <= n < |l| && n != k
          ensures l[k] + l[n] != 0
        {
          if n < i {
            // By precondition since n < i
          } else {
            // n >= i, and we know l[i] doesn't pair with anyone
            // Since k >= i, we can use the fact that l[i] doesn't pair with k or n
          }
        }
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
  // Trivial - exactly the precondition
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
    var found_pair := false;
    
    while j < |l| && !found_pair
      invariant 0 <= j <= |l|
      invariant !found_pair ==> forall m :: 0 <= m < j && m != i ==> l[i] + l[m] != 0
    {
      if j != i && l[i] + l[j] == 0 {
        found_pair := true;
      }
      j := j + 1;
    }
    
    if found_pair {
      return true;
    }
    
    // Update the invariant for the outer loop
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

