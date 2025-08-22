//ATOM
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
    requires n1 == |s1| && 0 <= n1 <= a.Length
    requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
    ensures Position == -1 || Position >= 1
    ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
{
  Position := 0;
  Count := 0;
  assume Position == -1 || Position >= 1;
  assume |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element;
  return Position, Count;
}

//IMPL Main
method Main() {
  /* code modified by LLM (iteration 1): Fixed array size to match sequence length and fixed assignment syntax */
  var a := new int[4];
  var b := [1,2,3,4];
  /* code modified by LLM (iteration 1): Fixed multiple assignment syntax */
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var n1 := |b|;
  var Element := 5;
  var Position, Count;
  Position, Count := FindPositionOfElement(a,Element,n1,b);
  print "position is ",Position;
}