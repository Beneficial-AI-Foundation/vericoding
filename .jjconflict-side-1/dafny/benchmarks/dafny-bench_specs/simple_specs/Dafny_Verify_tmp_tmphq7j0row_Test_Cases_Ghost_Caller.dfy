//ATOM

method M() returns (r: int) 
ensures r == 29
{
  r := 0;
  assume r ==> 29;
  return r;
}


//ATOM

function F(): int {
29
}


// SPEC

method Caller() {
}
