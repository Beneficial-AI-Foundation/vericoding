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
  var minVal := min(s[..]);
  
  /* code modified by LLM (iteration 1): Find first non-minimum element to initialize secondSmallest */
  var i := 0;
  while i < s.Length && s[i] == minVal
    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> s[k] == minVal
  {
    i := i + 1;
  }
  
  // i now points to the first element that is not the minimum
  secondSmallest := s[i];
  
  /* code modified by LLM (iteration 1): Find the actual minimum among all non-minVal elements */
  var j := 0;
  while j < s.Length
    invariant 0 <= j <= s.Length
    invariant secondSmallest != minVal
    invariant exists idx :: 0 <= idx < s.Length && s[idx] == secondSmallest
    invariant forall m :: 0 <= m < j && s[m] != minVal ==> s[m] >= secondSmallest
  {
    if s[j] != minVal && s[j] < secondSmallest {
      secondSmallest := s[j];
    }
    j := j + 1;
  }
}