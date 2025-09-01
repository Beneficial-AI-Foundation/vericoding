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
    assert is_sorted(a[0..] + a[..0]);
    return;
  }

  var n := |a|;
  var i := 0;
  
  // Find the first position where the sequence is not increasing
  while i < n - 1 && a[i] < a[i+1]
    invariant 0 <= i <= n - 1
    invariant forall k, l :: 0 <= k < l <= i ==> a[k] < a[l]
  {
    i := i + 1;
  }
  
  // If we reached the end, the array is already sorted
  if i == n - 1 {
    can := true;
    assert a[0..] + a[..0] == a;
    assert is_sorted(a);
    return;
  }
  
  // Now check if rotation at i+1 would work
  var rotation_point := i + 1;
  
  // Check if the rest of the array is sorted
  var j := rotation_point;
  while j < n - 1 && a[j] < a[j+1]
    invariant rotation_point <= j <= n - 1
    invariant forall k, l :: rotation_point <= k < l <= j ==> a[k] < a[l]
  {
    j := j + 1;
  }
  
  // If the second part is not fully sorted, we can't make it work
  if j < n - 1 {
    can := false;
    return;
  }
  
  // Check if the rotation would create a sorted array
  // The last element should be <= the first element of the rotated part
  if a[n-1] <= a[0] {
    can := true;
    assert is_sorted(a[rotation_point..]);
    assert is_sorted(a[..rotation_point]);
    assert a[rotation_point..] + a[..rotation_point] == a[rotation_point..] + a[..rotation_point];
  } else {
    can := false;
  }
}
// </vc-code>

