//ATOM
method F() returns ( r: int)
  ensures r <= 0
{
  r := 0;
  assume r <= 0;
  return r;
}

//IMPL 
method Main() 
{
  /* code modified by LLM (iteration 2): Main method implementation verified correctly */
  var x := F();
  x := x-1;
  print x;
}