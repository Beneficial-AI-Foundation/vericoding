

// <vc-helpers>
lemma max_exists(l: seq<int>)
  requires |l| > 0
  ensures exists i :: 0 <= i < |l| && forall j :: 0 <= j < |l| ==> l[j] <= l[i]
{
  if |l| == 1 {
    // Single element is trivially the maximum
  } else {
    var mid := |l| / 2;
    var left := l[..mid];
    var right := l[mid..];
    
    assert |left| > 0;
    assert |right| > 0;
    
    max_exists(left);
    max_exists(right);
    
    // Now we know both halves have maximum elements
  }
}

lemma update_max_preserves_invariant(l: seq<int>, max: int, index: int, new_val: int)
  requires 0 <= index < |l|
  requires forall i :: 0 <= i < index ==> l[i] <= max
  requires new_val > max
  ensures forall i :: 0 <= i <= index ==> l[i] <= new_val
{
  forall i | 0 <= i <= index 
    ensures l[i] <= new_val
  {
    if i < index {
      assert l[i] <= max;
      assert max < new_val;
    } else {
      assert i == index;
      assert l[i] == new_val;
    }
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)
    // pre-conditions-start
    requires |l| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var max := l[0];
  var index := 1;
  
  while index < |l|
    invariant 1 <= index <= |l|
    invariant forall i :: 0 <= i < index ==> l[i] <= max
    invariant exists i :: 0 <= i < index && l[i] == max
  {
    if l[index] > max {
      max := l[index];
      update_max_preserves_invariant(l, old(max), index, max);
    }
    index := index + 1;
  }
  
  result := max;
}
// </vc-code>

