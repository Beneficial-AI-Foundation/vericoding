//IMPL LinearSearch3

method LinearSearch3<T(==)>(data: array<T>, Element:T, s1:seq<T>) returns (position:int)
  requires |s1| <= data.Length
  requires forall i:: 0<= i <|s1| ==> s1[i] == data[data.Length -1-i]
  ensures position == -1 || position >= 1
  ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element && |s1| != 0
  // ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
  if |s1| == 0 {
    return -1;
  }
  
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant forall j :: 0 <= j < i ==> s1[j] != Element
  {
    if s1[i] == Element {
      return i + 1;
    }
    i := i + 1;
  }
  
  return -1;
}