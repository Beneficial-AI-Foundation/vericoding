method findMax(a: array<real>) returns (max: real)
 requires a.Length > 0
 ensures exists k :: 0 <= k < a.Length && max == a[k]
 ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{
  max := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant exists k :: 0 <= k < i && max == a[k]
    invariant forall k :: 0 <= k < i ==> max >= a[k]
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}


//IMPL 

// Test cases checked statically.
method testFindMax() {
  var a1 := new real[3];
  a1[0] := 1.0;
  a1[1] := 3.0;
  a1[2] := 2.0;
  
  var max1 := findMax(a1);
  /* code modified by LLM (iteration 1): added assertions to help Dafny prove that 3.0 is the maximum */
  assert a1[1] == 3.0;
  assert a1[0] <= 3.0 && a1[1] <= 3.0 && a1[2] <= 3.0;
  assert max1 >= a1[1];
  assert forall k :: 0 <= k < a1.Length ==> max1 >= a1[k];
  assert max1 == 3.0;
  
  var a2 := new real[1];
  a2[0] := 5.0;
  
  var max2 := findMax(a2);
  assert max2 == 5.0;
  
  var a3 := new real[4];
  a3[0] := -1.0;
  a3[1] := -5.0;
  a3[2] := -2.0;
  a3[3] := -3.0;
  
  var max3 := findMax(a3);
  /* code modified by LLM (iteration 1): added assertions to help Dafny prove that -1.0 is the maximum */
  assert a3[0] == -1.0;
  assert a3[0] >= a3[1] && a3[0] >= a3[2] && a3[0] >= a3[3];
  assert max3 >= a3[0];
  assert forall k :: 0 <= k < a3.Length ==> max3 >= a3[k];
  assert max3 == -1.0;
}