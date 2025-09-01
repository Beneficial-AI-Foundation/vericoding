function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
lemma IsSortedEmpty()
  ensures is_sorted([])
{
}

lemma IsSortedSingleton(x: int)
  ensures is_sorted([x])
{
}

lemma IsSortedConcat(a: seq<int>, b: seq<int>)
  requires is_sorted(a)
  requires is_sorted(b)
  requires |a| > 0 && |b| > 0 ==> a[|a|-1] <= b[0]
  ensures is_sorted(a + b)
{
}

lemma IsSortedRotation(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  requires |a| > 0
  requires forall k, l :: 0 <= k < l < i ==> a[k] < a[l]  // First part strictly increasing
  requires forall k, l :: i <= k < l < |a| ==> a[k] < a[l]  // Second part strictly increasing
  requires i > 0 && i < |a| ==> a[|a|-1] <= a[0]  // Wrap-around condition
  ensures is_sorted(a[i..] + a[..i])
{
  var rotated := a[i..] + a[..i];
  
  if i == 0 || i == |a| {
    assert rotated == a;
  } else {
    // The rotated sequence consists of a[i..] followed by a[..i]
    // Both parts are sorted due to strictly increasing property
    // The connection works because a[|a|-1] <= a[0]
  }
}
// </vc-helpers>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)
  // pre-conditions-start
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| == 1 {
    can := true;
    IsSortedSingleton(a[0]);
    assert a[0..] + a[..0] == [] + a == a;
    return;
  }

  var n := |a|;
  
  // Check if array is already sorted (rotation at 0)
  var sorted_from_start := true;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant sorted_from_start ==> forall k, l :: 0 <= k < l <= i ==> a[k] < a[l]
  {
    if a[i] >= a[i+1] {
      sorted_from_start := false;
      break;
    }
    i := i + 1;
  }
  
  if sorted_from_start {
    can := true;
    assert a[0..] + a[..0] == a + [] == a;
    assert is_sorted(a);
    return;
  }
  
  // Try each possible rotation point
  var rotation_found := false;
  var rot := 1;
  
  while rot < n && !rotation_found
    invariant 1 <= rot <= n
    invariant !rotation_found ==> forall r :: 1 <= r < rot ==> !is_sorted(a[r..] + a[..r])
  {
    // Check if rotating at position rot gives a sorted array
    var check_sorted := true;
    
    // Check if a[rot..] is strictly increasing
    var j := rot;
    while j < n - 1 && check_sorted
      invariant rot <= j <= n - 1
      invariant check_sorted ==> forall k, l :: rot <= k < l <= j ==> a[k] < a[l]
    {
      if a[j] >= a[j+1] {
        check_sorted := false;
      }
      j := j + 1;
    }
    
    if check_sorted {
      // Check if a[..rot] is strictly increasing
      j := 0;
      while j < rot - 1 && check_sorted
        invariant 0 <= j <= rot - 1
        invariant check_sorted ==> forall k, l :: 0 <= k < l <= j ==> a[k] < a[l]
      {
        if a[j] >= a[j+1] {
          check_sorted := false;
        }
        j := j + 1;
      }
      
      // Check the wrap-around condition
      if check_sorted && a[n-1] > a[0] {
        check_sorted := false;
      }
      
      if check_sorted {
        rotation_found := true;
        IsSortedRotation(a, rot);
        assert is_sorted(a[rot..] + a[..rot]);
      }
    }
    
    rot := rot + 1;
  }
  
  can := rotation_found;
}
// </vc-code>

