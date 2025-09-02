//ATOM
method leq(a: array<int>, b: array<int>) returns (result: bool) 
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
  /* code modified by LLM (iteration 1): fixed compilation errors - changed ==> to == for array equality comparisons */
  result := false;
  assume result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k]);
  return result;
}

//IMPL testLeq
method testLeq() {
  var a1 := new int[3];
  a1[0] := 1; a1[1] := 2; a1[2] := 3;
  
  var b1 := new int[4];
  b1[0] := 1; b1[1] := 2; b1[2] := 3; b1[3] := 4;
  
  var result1 := leq(a1, b1);
  
  var a2 := new int[2];
  a2[0] := 1; a2[1] := 3;
  
  var b2 := new int[2];
  b2[0] := 1; b2[1] := 2;
  
  var result2 := leq(a2, b2);
  
  var a3 := new int[2];
  a3[0] := 5; a3[1] := 6;
  
  var b3 := new int[2];
  b3[0] := 5; b3[1] := 6;
  
  var result3 := leq(a3, b3);
}