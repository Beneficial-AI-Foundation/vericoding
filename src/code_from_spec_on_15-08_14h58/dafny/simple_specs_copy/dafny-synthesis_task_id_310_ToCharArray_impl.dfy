//IMPL
method ToCharArray(s: string) returns (a: array<char>)
  ensures a.Length == |s|
  ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{
  a := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> a[j] == s[j]
  {
    a[i] := s[i];
    i := i + 1;
  }
}