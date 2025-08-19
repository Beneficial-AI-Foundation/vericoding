//ATOM
method F() returns ( r: int)
  ensures r <= 0
{
  r := 0;
  assume r <= 0;
  return r;
}

//IMPL Main
method Main() 
{
  /* code modified by LLM (iteration 1): Added proper variable declaration and method call */
  var x := F();
  x := x-1;
  print x;
}