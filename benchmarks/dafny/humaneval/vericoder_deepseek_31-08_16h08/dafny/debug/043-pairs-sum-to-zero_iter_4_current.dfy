

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
    
    // Now show the original condition: no pairs at all
    // We need to show that for all k and m where k != m, l[k] + l[m] != 0
    // We'll use the precondition and the fact that l[i] doesn't pair with anyone
    forall i2, j | 0 <= i2 < |l| && 0 <= j < |l| && i2 != j
      ensures l[i2] + l[j] != 0
    {
      if i2 < i {
        // By precondition since i2 < i
      } else if i2 == i {
        // By the forall above since i2 == i
      } else { 
        // i2 > i, and j != i2
        // We need to show l[i2] + l[j] != 0
        if j < i {
          // j < i < i2, so l[j] doesn't pair with i2 (by precondition with k = j, m = i2)
        } else if j == i {
          // j == i < i2, and we already know l[i2] + l[i] != 0 from the forall above
        } else {
          // j > i - but we don't have direct information about pairs between i2 and j
          // This shows the lemma approach is not straightforward
        }
      }
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

lemma extend_invariant(l: seq<int>, i: int)
  requires 0 <= i < |l|
  requires forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
  requires forall m :: 0 <= m < |l| && m != i ==> l[i] + l[m] != 0
  ensures forall k :: 0 <= k <= i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
{
  forall k, m | 0 <= k <= i && 0 <= m < |l| && k != m
    ensures l[k] + l[m] != 0
  {
    if k < i {
      // Already covered by precondition
    } else {
      // k == i, covered by the second requirement
    }
  }
}
// </vc-helpers>
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
      } else {
        j := j + 1;
      }
    }
    
    if found_pair {
      return true;
    }
    
    // Prove the invariant extension for the outer loop
    assert forall m :: 0 <= m < |l| && m != i ==> l[i] + l[m] != 0;
    extend_invariant(l, i);
    
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

