//IMPL 
method ToCharArray(s: string) returns (a: array<char>)
  ensures a.Length == |s|
  ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{
  a := new char[|s|](i requires 0 <= i < |s| => s[i]);
}