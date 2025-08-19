//ATOM
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
    requires n1 == |s1| && 0 <= n1 <= a.Length
    requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
    ensures Position == -1 || Position >= 1
    ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
{
  /* code modified by LLM (iteration 1): removed invalid assume statements and implemented proper search logic */
  Position := -1;
  Count := 0;
  
  var i := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant Position == -1 || (1 <= Position <= n1)
    invariant Position >= 1 ==> (Position-1 < |s1| && s1[Position-1] == Element)
    invariant Position == -1 ==> forall j:: 0 <= j < i ==> s1[j] != Element
  {
    if a[i] == Element {
      Position := i + 1; // 1-based indexing as per ensures clause
      Count := Count + 1;
      return Position, Count;
    }
    i := i + 1;
  }
  
  return Position, Count;
}

//IMPL 
method Main() {
  /* code modified by LLM (iteration 1): added array initialization and bounds checking */
  var a := new int[5];
  var b := [1,2,3,4];
  a[0],a[1],a[2],a[3]:= 1,2,3,4;
  var n1 := |b|;
  var Element := 5;
  var Position, Count;
  Position, Count := FindPositionOfElement(a,Element,n1,b);
  print "position is ",Position;
}