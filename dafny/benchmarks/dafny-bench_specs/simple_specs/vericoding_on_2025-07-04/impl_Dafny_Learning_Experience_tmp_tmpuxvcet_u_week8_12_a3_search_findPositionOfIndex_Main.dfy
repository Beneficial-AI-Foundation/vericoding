//ATOM
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
    requires n1 == |s1| && 0 <= n1 <= a.Length
    requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
    ensures Position == -1 || Position >= 1
    ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly search for element and removed assume statements */
  Position := -1;
  Count := 0;
  
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant Position == -1 || Position >= 1
    invariant Position >= 1 ==> 0 <= Position - 1 < i && s1[Position - 1] == Element
    invariant Position == -1 ==> forall j :: 0 <= j < i ==> s1[j] != Element
    invariant Count == (if Position >= 1 then 1 else 0)
  {
    if s1[i] == Element && Position == -1 {
      Position := i + 1; // 1-based indexing as per ensures clause
      Count := 1;
    }
    i := i + 1;
  }
  
  return Position, Count;
}

method Main() {
  var a := new int[5];
  var b := [1,2,3,4];
  a[0],a[1],a[2],a[3]:= 1,2,3,4;
  var n1 := |b|;
  var Element := 5;
  var Position, Count;
  Position, Count := FindPositionOfElement(a,Element,n1,b);
  print "position is ",Position;
}