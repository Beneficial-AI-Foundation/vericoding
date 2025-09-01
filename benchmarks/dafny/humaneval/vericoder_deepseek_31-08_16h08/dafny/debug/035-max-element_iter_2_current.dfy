

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
    }
    index := index + 1;
  }
  
  result := max;
}
// </vc-code>

