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
  /* code modified by LLM (iteration 1): store minimum value and initialize variables */
  var minimum := min(s[..]);
  var i := 0;
  var minIndex := -1;
  
  /* code modified by LLM (iteration 1): find minimum index with corrected invariant */
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant minimum == min(s[..])
    invariant minIndex == -1 ==> forall j :: 0 <= j < i ==> s[j] != minimum
    invariant minIndex != -1 ==> 0 <= minIndex < i && s[minIndex] == minimum
  {
    if s[i] == minimum {
      minIndex := i;
      break;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): assert minIndex was found using precondition */
  assert minIndex != -1;
  
  /* code modified by LLM (iteration 1): initialize secondSmallest with first non-minimum value */
  i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant minimum == min(s[..])
    invariant minIndex != -1 && 0 <= minIndex < s.Length && s[minIndex] == minimum
  {
    if s[i] != minimum {
      secondSmallest := s[i];
      break;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): find actual second smallest value */
  i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant minimum == min(s[..])
    invariant minIndex != -1 && 0 <= minIndex < s.Length && s[minIndex] == minimum
    invariant secondSmallest != minimum
    invariant forall k :: 0 <= k < i && s[k] != minimum ==> s[k] >= secondSmallest
    invariant exists k :: 0 <= k < s.Length && s[k] == secondSmallest
  {
    if s[i] != minimum && s[i] < secondSmallest {
      secondSmallest := s[i];
    }
    i := i + 1;
  }
}