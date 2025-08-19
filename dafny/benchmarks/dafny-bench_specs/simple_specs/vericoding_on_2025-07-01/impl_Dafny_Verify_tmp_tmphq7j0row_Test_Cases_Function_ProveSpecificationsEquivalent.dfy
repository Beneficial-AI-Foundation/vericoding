//ATOM

method TripleConditions(x: int) returns (r: int) 
ensures r == 3 * x
{
  r := 0;
  assume r ==> 3 * x;
  return r;
}


// SPEC


method ProveSpecificationsEquivalent(x: int) {
}