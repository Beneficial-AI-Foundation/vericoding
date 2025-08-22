/* 
* Formal verification of a simple algorithm to find the maximum value in an array.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Finds the maximum value in a non-empty array.
//IMPL findMax

// Finds the maximum value in a non-empty array.
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



// Test cases checked statically.
//IMPL testFindMax


// Test cases checked statically.
method testFindMax() {
  var a1 := new real[3];
  a1[0] := 1.0;
  a1[1] := 3.0;
  a1[2] := 2.0;
  var max1 := findMax(a1);
  /* code modified by LLM (iteration 1): Added explicit assertion about array contents to help Dafny prove the result */
  assert a1[1] == 3.0 && (forall k :: 0 <= k < a1.Length ==> a1[k] <= 3.0);
  assert max1 == 3.0;
  
  var a2 := new real[1];
  a2[0] := 5.0;
  var max2 := findMax(a2);
  /* code modified by LLM (iteration 1): Added explicit assertion about array contents to help Dafny prove the result */
  assert a2[0] == 5.0;
  assert max2 == 5.0;
  
  var a3 := new real[4];
  a3[0] := -1.0;
  a3[1] := -5.0;
  a3[2] := -2.0;
  a3[3] := -10.0;
  var max3 := findMax(a3);
  /* code modified by LLM (iteration 1): Added explicit assertion about array contents to help Dafny prove the result */
  assert a3[0] == -1.0 && (forall k :: 0 <= k < a3.Length ==> a3[k] <= -1.0);
  assert max3 == -1.0;
}