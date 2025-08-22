//IMPL FindSmallest
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{
  min := s[0];
  var j := 1;
  
  while j < s.Length
    invariant 1 <= j <= s.Length
    invariant forall k :: 0 <= k < j ==> min <= s[k]
    invariant exists k :: 0 <= k < j && min == s[k]
  {
    if s[j] < min {
      min := s[j];
    }
    j := j + 1;
  }
}