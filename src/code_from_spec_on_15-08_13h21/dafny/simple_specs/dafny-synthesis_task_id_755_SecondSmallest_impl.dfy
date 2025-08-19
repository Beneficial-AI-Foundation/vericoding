function min(s: seq<int>) : (r: int)
  requires |s| >= 2
  ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
  if |s| == 2 then MinPair(s)
  else MinPair([s[0], min(s[1..])])
}


//ATOM
function MinPair(s: seq<int>) : (r: int)
  requires |s| == 2
  ensures s[0] <= s[1] <==> r == s[0]
  ensures s[0] > s[1] ==> r == s[1] 
{
  if s[0] <= s[1] then s[0] else s[1]
}


//IMPL


method SecondSmallest(s: array<int>) returns (secondSmallest: int)
  requires s.Length >= 2
  // There must be at least 2 different values, a minimum and another one
  requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
  ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
  ensures forall k :: 0 <= k < s.Length && s[k] != min(s[..]) ==> s[k] >= secondSmallest
{
  var minVal := min(s[..]);
  secondSmallest := s[0];
  
  // Find the first non-minimum value as initial secondSmallest
  var i := 0;
  while i < s.Length && s[i] == minVal
    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> s[k] == minVal
  {
    i := i + 1;
  }
  
  secondSmallest := s[i];
  
  // Find the actual second smallest among all non-minimum values
  var j := 0;
  while j < s.Length
    invariant 0 <= j <= s.Length
    invariant forall k :: 0 <= k < j && s[k] != minVal ==> s[k] >= secondSmallest
    invariant exists idx :: 0 <= idx < s.Length && s[idx] != minVal && s[idx] == secondSmallest
  {
    if s[j] != minVal && s[j] < secondSmallest {
      secondSmallest := s[j];
    }
    j := j + 1;
  }
}