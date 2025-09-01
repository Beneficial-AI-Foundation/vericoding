function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
function is_sorted_helper(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

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

lemma min_index_properties(a: seq<int>, min_index: int, min_val: int)
  requires |a| > 0
  requires 0 <= min_index < |a|
  requires min_val == a[min_index]
  requires forall k :: 0 <= k < |a| ==> a[k] >= min_val
  ensures forall k :: 0 <= k < min_index ==> a[k] > min_val
{
  var k: int := 0;
  while k < min_index
    invariant 0 <= k <= min_index
    invariant forall j :: 0 <= j < k ==> a[j] > min_val
  {
    assert a[k] >= min_val;
    if a[k] == min_val {
      assert false;
    }
    k := k + 1;
  }
}

lemma sorted_rotation_properties(a: seq<int>, min_val: int)
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  requires forall k :: 0 <= k < |a| ==> a[k] >= min_val
  ensures exists i :: 0 <= i < |a| && a[i] == min_val && is_sorted_helper(a[i..] + a[..i]) <==> 
           exists i :: 0 <= i < |a| && is_sorted_helper(a[i..] + a[..i])
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
  
  if n == 1 {
    can := true;
    return;
  }
  
  var first := a[0];
  var min_val := first;
  var min_index := 0;
  var idx := 1;
  
  while idx < n
    invariant 1 <= idx <= n
    invariant 0 <= min_index < n
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
  
  assert forall k :: 0 <= k < n ==> a[k] >= min_val;
  
  min_index_properties(a, min_index, min_val);
  
  var rotated := a[min_index..] + a[..min_index];
  
  assert |rotated| == n && rotated[0] == min_val;
  
  can := is_sorted_helper(rotated);
  
  if can {
    return;
  }
  
  idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant !can
    invariant forall k :: 0 <= k < idx ==> !is_sorted_helper(a[k..] + a[..k])
    decreases n - idx
  {
    if idx != min_index {
      var test_rotated := a[idx..] + a[..idx];
      if is_sorted_helper(test_rotated) {
        can := true;
        return;
      }
    }
    idx := idx + 1;
  }
}
// </vc-code>

