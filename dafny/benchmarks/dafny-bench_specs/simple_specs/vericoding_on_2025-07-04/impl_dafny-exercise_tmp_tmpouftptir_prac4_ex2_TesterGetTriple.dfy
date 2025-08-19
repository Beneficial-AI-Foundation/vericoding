//ATOM
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}


//ATOM

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] && a[index + 1] == a[index + 2]
{
  index := 0;
  assume 0 <= index < a.Length - 2 || index == a.Length;
  assume index == a.Length <==> !triple(a);
  assume 0 <= index < a.Length - 2 <==> triple(a);
  assume 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] && a[index + 1] == a[index + 2];
  return index;
}


//IMPL 

method TesterGetTriple()
{
  // Test case 1: Array with a triple at the beginning
  var a1 := new int[5];
  a1[0], a1[1], a1[2], a1[3], a1[4] := 1, 1, 1, 2, 3;
  var result1 := GetTriple(a1);
  /* code modified by LLM (iteration 1): Added assertion to establish triple(a1) before calling GetTriple */
  assert triple(a1) by {
    assert a1[0] == a1[1] && a1[1] == a1[2];
    assert 0 <= 0 < a1.Length - 2;
  }
  assert 0 <= result1 < a1.Length - 2;
  assert a1[result1] == a1[result1 + 1] && a1[result1 + 1] == a1[result1 + 2];
  
  // Test case 2: Array with a triple in the middle
  var a2 := new int[5];
  a2[0], a2[1], a2[2], a2[3], a2[4] := 1, 2, 2, 2, 3;
  var result2 := GetTriple(a2);
  /* code modified by LLM (iteration 1): Added assertion to establish triple(a2) before calling GetTriple */
  assert triple(a2) by {
    assert a2[1] == a2[2] && a2[2] == a2[3];
    assert 0 <= 1 < a2.Length - 2;
  }
  assert 0 <= result2 < a2.Length - 2;
  assert a2[result2] == a2[result2 + 1] && a2[result2 + 1] == a2[result2 + 2];
  
  // Test case 3: Array with no triple
  var a3 := new int[4];
  a3[0], a3[1], a3[2], a3[3] := 1, 2, 1, 2;
  var result3 := GetTriple(a3);
  /* code modified by LLM (iteration 1): Added assertion to establish !triple(a3) before calling GetTriple */
  assert !triple(a3) by {
    assert a3[0] != a3[1];
    assert a3[1] != a3[2];
    assert forall i :: 0 <= i < a3.Length - 2 ==> !(a3[i] == a3[i + 1] && a3[i + 1] == a3[i + 2]);
  }
  assert result3 == a3.Length;
  
  // Test case 4: Array too small to have a triple
  var a4 := new int[2];
  a4[0], a4[1] := 1, 1;
  var result4 := GetTriple(a4);
  /* code modified by LLM (iteration 1): Added assertion to establish !triple(a4) before calling GetTriple */
  assert !triple(a4) by {
    assert a4.Length - 2 == 0;
    assert forall i :: 0 <= i < a4.Length - 2 ==> false;
  }
  assert result4 == a4.Length;
}