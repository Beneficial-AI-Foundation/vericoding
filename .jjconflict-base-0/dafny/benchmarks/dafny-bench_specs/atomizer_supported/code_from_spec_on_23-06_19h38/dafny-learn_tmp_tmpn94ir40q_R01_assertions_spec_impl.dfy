// IMPL 
method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}


// IMPL 
method TestingAbs()
{
  var result := Abs(-5);
  assert result == 5;
  
  var result2 := Abs(3);
  assert result2 == 3;
  
  var result3 := Abs(0);
  assert result3 == 0;
}


// IMPL 
method TestingAbs2()
{
  var x := Abs(-10);
  assert x >= 0;
  assert x == 10;
  
  var y := Abs(7);
  assert y >= 0;
  assert y == 7;
}


// IMPL 
method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
  /* code modified by LLM (iteration 1): added postcondition to specify which value is returned */
  ensures c == a || c == b
{
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

// IMPL 
method TestingMax() {
  var result := Max(5, 3);
  assert result == 5;
  assert result >= 5;
  assert result >= 3;
  
  var result2 := Max(2, 8);
  assert result2 == 8;
  assert result2 >= 2;
  assert result2 >= 8;
  
  var result3 := Max(4, 4);
  assert result3 == 4;
  assert result3 >= 4;
}