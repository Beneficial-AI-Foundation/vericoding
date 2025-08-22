//ATOM


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
  var minimum := min(s[..]);
  var candidate := s[0];
  
  // Find the first element that's not the minimum
  var i := 0;
  while i < s.Length && s[i] == minimum
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> s[j] == minimum
  {
    i := i + 1;
  }
  
  if i < s.Length {
    secondSmallest := s[i];
  } else {
    secondSmallest := s[0]; // This shouldn't happen given the precondition
  }
  
  // Find the actual second smallest among all non-minimum values
  i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant exists j :: 0 <= j < s.Length && s[j] != minimum && s[j] == secondSmallest
    invariant forall k :: 0 <= k < i && s[k] != minimum ==> s[k] >= secondSmallest
  {
    if s[i] != minimum && s[i] < secondSmallest {
      secondSmallest := s[i];
    }
    i := i + 1;
  }
}