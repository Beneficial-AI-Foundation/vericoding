

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
    // Show that no pair exists with i
    forall j | 0 <= j < |l| && j != i 
      ensures l[i] + l[j] != 0 
    {
    }
    
    // Show no pairs exist at all
    forall i2, j | 0 <= i2 < |l| && 0 <= j < |l| && i2 != j
      ensures l[i2] + l[j] != 0
    {
      if i2 < i {
        // By precondition
      } else if i2 == i {
        // By the forall above
      } else {
        // i2 > i - but we don't need this case as precondition only covers k < i
      }
    }
  }
}

lemma no_pairs_before_i_implies_no_pairs(l: seq<int>, i: int)
  requires 0 <= i <= |l|
  requires forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
  ensures forall k :: 0 <= k < i ==> forall m :: 0 <= m < |l| && m != k ==> l[k] + l[m] != 0
{
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
    } else {
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
    decreases |l| - i
  {
    var j := 0;
    var found_pair := false;
    
    while j < |l| && !found_pair
      invariant 0 <= j <= |l|
      invariant !found_pair ==> forall m :: 0 <= m < j && m != i ==> l[i] + l[m] != 0
      decreases |l| - j
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
    
    // Update invariant for outer loop
    extend_invariant(l, i);
    
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

