//ATOM
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}


//ATOM

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
  index := 0;
  assume 0 <= index < a.Length - 2 || index == a.Length;
  assume index == a.Length <==> !triple(a);
  assume 0 <= index < a.Length - 2 <==> triple(a);
  assume 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2];
  return index;
}


//IMPL TesterGetTriple
method TesterGetTriple()
{
  // Test case 1: Array with a triple
  var a1 := new int[5];
  a1[0] := 1;
  a1[1] := 2;
  a1[2] := 2;
  a1[3] := 2;
  a1[4] := 3;
  
  /* code modified by LLM (iteration 1): Added witness for triple existence */
  assert a1[1] == a1[2] == a1[3] == 2;
  assert 0 <= 1 < a1.Length - 2 && a1[1] == a1[1 + 1] == a1[1 + 2];
  assert triple(a1) by {
    assert exists i :: 0 <= i < a1.Length - 2 && a1[i] == a1[i + 1] == a1[i + 2];
  }
  
  var result1 := GetTriple(a1);
  assert triple(a1);
  assert result1 == 1;
  
  // Test case 2: Array without a triple
  var a2 := new int[4];
  a2[0] := 1;
  a2[1] := 2;
  a2[2] := 3;
  a2[3] := 4;
  
  /* code modified by LLM (iteration 1): Added proof that no triple exists */
  assert !triple(a2) by {
    assert a2[0] != a2[1]; // 1 != 2
    assert a2[1] != a2[2]; // 2 != 3
    assert forall i :: 0 <= i < a2.Length - 2 ==> !(a2[i] == a2[i + 1] == a2[i + 2]);
  }
  
  var result2 := GetTriple(a2);
  assert !triple(a2);
  assert result2 == a2.Length;
}