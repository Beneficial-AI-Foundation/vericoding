//IMPL 

method LinearSearch2<T(==)>(data: array<T>, Element:T, s1:seq<T>) returns (position:int)
  requires |s1| <= data.Length
  requires forall i:: 0<= i <|s1| ==> s1[i] == data[i]
  ensures position == -1 || position >= 1
  ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element
  ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant forall j :: 0 <= j < i ==> s1[j] != Element
  {
    if data[i] == Element {
      position := i + 1;
      return;
    }
    i := i + 1;
  }
  position := -1;
}