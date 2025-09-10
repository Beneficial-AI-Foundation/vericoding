predicate ValidInput(s: string)
{
    |s| >= 0 && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'B', 'C', '.'}
}

predicate HasAllThreeColors(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    'A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3]
}

predicate PossibleToGetAllColors(s: string)
{
    |s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i)
}

// <vc-helpers>
lemma WindowHasAllThreeColors(s: string, start: int)
  requires 0 <= start <= |s| - 3
  ensures HasAllThreeColors(s, start) == ('A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3])
{
}

lemma ValidInputChars(s: string, i: int)
  requires ValidInput(s)
  requires 0 <= i < |s|
  ensures s[i] in {'A', 'B', 'C', '.'}
{
}

lemma SliceHasChar(s: string, start: int, end: int, ch: char, j: int)
  requires 0 <= start <= end <= |s|
  requires 0 <= j < end - start
  ensures ch in s[start..end] <==> (s[start+j] == ch || ch in s[start..start+j] || ch in s[start+j+1..end])
{
}

lemma SliceProperties(s: string, start: int, end: int, ch: char)
  requires 0 <= start <= end <= |s|
  ensures ch in s[start..end] <==> exists k :: start <= k < end && s[k] == ch
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
  if |s| < 3 {
    result := "No";
    return;
  }
  
  var i := 0;
  while i <= |s| - 3
    invariant 0 <= i <= |s| - 2
    invariant forall j :: 0 <= j < i ==> !HasAllThreeColors(s, j)
  {
    var hasA := false;
    var hasB := false;
    var hasC := false;
    var j := 0;
    
    while j < 3
      invariant 0 <= j <= 3
      invariant hasA == (exists k :: 0 <= k < j && s[i+k] == 'A')
      invariant hasB == (exists k :: 0 <= k < j && s[i+k] == 'B')
      invariant hasC == (exists k :: 0 <= k < j && s[i+k] == 'C')
    {
      var ch := s[i + j];
      if ch == 'A' { hasA := true; }
      else if ch == 'B' { hasB := true; }
      else if ch == 'C' { hasC := true; }
      j := j + 1;
    }
    
    if hasA && hasB && hasC {
      result := "Yes";
      return;
    }
    
    i := i + 1;
  }
  
  result := "No";
}
// </vc-code>

