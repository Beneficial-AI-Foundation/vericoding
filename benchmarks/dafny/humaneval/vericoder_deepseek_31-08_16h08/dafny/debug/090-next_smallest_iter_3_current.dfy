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
}

lemma MaxInSliceLemma(s: seq<int>, maxVal: int, i: int)
  requires 0 <= i <= |s|
  requires maxVal in s[0..i]
  requires forall x :: x in s[0..i] ==> x <= maxVal
  ensures maxVal in s[0..i]
  ensures forall x :: x in s[0..i] ==> x <= maxVal
{
}

lemma EstablishGlobalMax(s: seq<int>, maxVal: int, i: int)
  requires |s| > 0
  requires 0 <= i <= |s|
  requires maxVal in s[0..i]
  requires forall x :: x in s[0..i] ==> x <= maxVal
  requires i == |s|
  ensures forall x :: x in s ==> x <= maxVal
{
}
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
      i := i + 1;
    }
    
    // Establish that maxVal is indeed the global maximum
    EstablishGlobalMax(s, maxVal, i);
    
    // Now the preconditions for MaxPropertyForPairs are satisfied
    MaxPropertyForPairs(s, maxVal);
    res := Some(maxVal);
  }
}
// </vc-code>

