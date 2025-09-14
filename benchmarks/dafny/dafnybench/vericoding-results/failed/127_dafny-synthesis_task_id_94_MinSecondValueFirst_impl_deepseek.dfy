

// <vc-helpers>
function MinHelper(s: array<seq<int>>, i: int, j: int): bool
  requires 0 <= i < s.Length
  requires 0 <= j <= s.Length
  ensures j == s.Length ==> forall k :: 0 <= k < s.Length ==> s[i][1] <= s[k][1]
  ensures j < s.Length && result ==> s[i][1] <= s[j][1] && MinHelper(s, i, j+1)
  ensures j < s.Length && !result ==> !(s[i][1] <= s[j][1] && MinHelper(s, i, j+1))
{
  if j >= s.Length then
    true
  else
    s[i][1] <= s[j][1] && MinHelper(s, i, j+1)
}
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
// </vc-spec>
// <vc-code>
{
  var minIndex := 0;
  var i := 1;
  
  while i < s.Length
    invariant 0 <= minIndex < s.Length
    invariant 1 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> s[minIndex][1] <= s[k][1]
  {
    if s[i][1] < s[minIndex][1] {
      minIndex := i;
    }
    i := i + 1;
  }
  
  firstOfMinSecond := s[minIndex][0];
}
// </vc-code>

