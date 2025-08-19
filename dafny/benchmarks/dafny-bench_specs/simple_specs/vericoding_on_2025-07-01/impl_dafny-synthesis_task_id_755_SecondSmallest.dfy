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
  var found := false;
  var i := 0;
  
  // Find the first non-minimum value to initialize secondSmallest
  while i < s.Length && !found
    invariant 0 <= i <= s.Length
    invariant !found ==> forall j :: 0 <= j < i ==> s[j] == minimum
  {
    if s[i] != minimum {
      secondSmallest := s[i];
      found := true;
    }
    i := i + 1;
  }
  
  // Continue through the array to find the actual second smallest
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant secondSmallest != minimum
    invariant exists j :: 0 <= j < s.Length && s[j] == secondSmallest
    invariant forall j :: 0 <= j < i && s[j] != minimum ==> s[j] >= secondSmallest
  {
    if s[i] != minimum && s[i] < secondSmallest {
      secondSmallest := s[i];
    }
    i := i + 1;
  }
}