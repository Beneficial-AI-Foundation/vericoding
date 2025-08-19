//ATOM
method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
{
  flag := false;
  assume flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1];
  assume flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1];
  return flag;
}

//IMPL Main
method Main() {
  /* code modified by LLM (iteration 1): Fixed array initialization syntax - arrays must be allocated with 'new' and length, then elements assigned individually */
  var data1 := new int[5];
  data1[0] := 1;
  data1[1] := 2;
  data1[2] := 3;
  data1[3] := 2;
  data1[4] := 1;
  var f1 := Symmetric(data1);
  
  /* code modified by LLM (iteration 1): Fixed array initialization syntax for second array */
  var data2 := new int[2];
  data2[0] := 1;
  data2[1] := 2;
  var f2 := Symmetric(data2);
  //print f2;
}