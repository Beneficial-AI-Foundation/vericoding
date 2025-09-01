function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
lemma window_lemma(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= |s|
  ensures s[i..k] == s[i..j] + s[j..k]
{
}

lemma rotate_equivalence(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures a[i..] + a[..i] == a[i..|a|] + a[0..i]
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
  can := false;
  var n := |a|;
  var first := a[0];
  var min_val := first;
  var min_index := 0;
  
  // Find the index of minimum element
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant min_val == a[min_index]
    invariant forall k :: 0 <= k < idx ==> a[k] >= min_val
    decreases n - idx
  {
    if a[idx] < min_val {
      min_val := a[idx];
      min_index := idx;
    }
    idx := idx + 1;
  }
  
  // Check if sequence from min_index is sorted
  var rotated := a[min_index..] + a[..min_index];
  can := is_sorted(rotated);
  
  // Check if there are multiple minimums that could work
  idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant can ==> is_sorted(a[min_index..] + a[..min_index])
    invariant !can ==> forall k :: 0 <= k < idx ==> !is_sorted(a[k..] + a[..k])
    decreases n - idx
  {
    if a[idx] == min_val && idx != min_index {
      var test_rotated := a[idx..] + a[..idx];
      if is_sorted(test_rotated) {
        can := true;
      }
    }
    idx := idx + 1;
  }
}
// </vc-code>

