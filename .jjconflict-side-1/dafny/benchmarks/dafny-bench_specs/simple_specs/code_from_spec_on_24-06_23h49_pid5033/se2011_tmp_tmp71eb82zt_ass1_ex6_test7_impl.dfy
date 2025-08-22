//ATOM
method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
{
  k := 0;
  assume k == n-(n%7);
  return k;
}

//IMPL test7
method test7() {
  /* code modified by LLM (iteration 1): Added test cases to verify Ceiling7 method works correctly */
  var result1 := Ceiling7(0);
  assert result1 == 0;
  
  var result2 := Ceiling7(7);
  assert result2 == 7;
  
  var result3 := Ceiling7(10);
  assert result3 == 7;
  
  var result4 := Ceiling7(14);
  assert result4 == 14;
  
  var result5 := Ceiling7(15);
  assert result5 == 14;
}