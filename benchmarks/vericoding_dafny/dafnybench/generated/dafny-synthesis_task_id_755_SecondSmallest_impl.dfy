// <vc-spec>
function MinPair(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1] 
{
    if s[0] <= s[1] then s[0] else s[1]
}


function min(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
    if |s| == 2 then MinPair(s)
    else MinPair([s[0], min(s[1..])])
}

// <vc-helpers>
// </vc-helpers>

method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
// </vc-spec>
// <vc-code>
{
  var minVal := min(s[..]);
  var found := false;
  var i := 0;
  
  // Find the first element that is greater than min
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant !found ==> forall k :: 0 <= k < i ==> s[k] == minVal
  {
    if s[i] > minVal {
      secondSmallest := s[i];
      found := true;
      break;
    }
    i := i + 1;
  }
  
  // Now find the minimum among all elements > minVal
  i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant found
    invariant secondSmallest > minVal
    invariant exists j :: 0 <= j < s.Length && s[j] == secondSmallest && s[j] > minVal
    invariant forall k :: 0 <= k < i && s[k] > minVal ==> s[k] >= secondSmallest
  {
    if s[i] > minVal && s[i] < secondSmallest {
      secondSmallest := s[i];
    }
    i := i + 1;
  }
}
// </vc-code>