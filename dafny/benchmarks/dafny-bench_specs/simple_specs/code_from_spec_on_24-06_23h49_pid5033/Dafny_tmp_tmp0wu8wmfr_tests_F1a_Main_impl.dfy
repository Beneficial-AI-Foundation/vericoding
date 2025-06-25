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
  var x := F();
  x := x-1;
  print x;
}