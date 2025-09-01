datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MaxIndexExists(s: seq<int>, maxVal: int)
  requires |s| > 0
  requires maxVal in s
  requires forall x :: x in s ==> x <= maxVal
  ensures exists i :: 0 <= i < |s| && s[i] == maxVal
{
}

lemma MaxPropertyForPairs(s: seq<int>, maxVal: int)
  requires |s| > 0
  requires maxVal in s
  requires forall x :: x in s ==> x <= maxVal
  ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= maxVal || s[y] <= maxVal
{
  // The key insight: since maxVal is the maximum and it's in the sequence,
  // for any pair (x,y), at least one must be <= maxVal because maxVal itself
  // is one of the elements that could be either x or y in the pair
}

lemma MaxInSliceLemma(s: seq<int>, maxVal: int, i: int)
  requires 0 <= i <= |s|
  requires maxVal in s[0..i]
  requires forall x :: x in s[0..i] ==> x <= maxVal
  ensures maxVal in s[0..i]
  ensures forall x :: x in s[0..i] ==> x <= maxVal
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method rolling_max(s: seq<int>) returns (res: Option<int>) 
    // post-conditions-start
    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| < 2 {
    res := None;
  } else {
    var maxVal := s[0];
    var i := 1;
    
    while i < |s|
      invariant 1 <= i <= |s|
      invariant maxVal in s[0..i]
      invariant forall x :: x in s[0..i] ==> x <= maxVal
    {
      if s[i] > maxVal {
        maxVal := s[i];
      }
      MaxInSliceLemma(s, maxVal, i+1);
      i := i + 1;
    }
    
    // Before calling MaxPropertyForPairs, we need to establish its preconditions
    assert |s| > 0;
    assert maxVal in s;
    assert forall x :: x in s ==> x <= maxVal
      by {
        var j := 0;
        while j < |s|
          invariant 0 <= j <= |s|
          invariant forall x :: x in s[0..j] ==> x <= maxVal
        {
          j := j + 1;
        }
      };
    
    MaxPropertyForPairs(s, maxVal);
    res := Some(maxVal);
  }
}
// </vc-code>

