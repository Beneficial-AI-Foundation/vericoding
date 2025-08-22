//ATOM
method MaxSum(x:int, y:int) returns (s:int, m:int)
  ensures s == x+y
  ensures (m == x || m == y) && x <= m && y <= m
{
  s := 0;
  m := 0;
  assume s == x+y;
  assume (m == x || m == y) && x <= m && y <= m;
  return s, m;
}

//IMPL
method Main() 
{
 var m, n := 4,5;
 var a,b := MaxSum(m,n);
 print "Search return a is ", a,",,,,, b is ", b, "\n";
}