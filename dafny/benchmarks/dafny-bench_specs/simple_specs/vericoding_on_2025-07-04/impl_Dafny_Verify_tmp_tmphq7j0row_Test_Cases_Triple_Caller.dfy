//ATOM

method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
  r := 0;
  assume r ==> 3 * x;
  return r;
}


//IMPL 

method Caller() {
}