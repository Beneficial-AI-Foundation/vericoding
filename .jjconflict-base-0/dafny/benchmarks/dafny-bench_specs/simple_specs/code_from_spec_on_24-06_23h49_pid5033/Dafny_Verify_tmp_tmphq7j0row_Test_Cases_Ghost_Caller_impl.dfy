//ATOM
method M() returns (r: int) 
ensures r == 29
{
  r := 0;
  assume r == 29;
  return r;
}

//ATOM
function F(): int {
29
}

//IMPL
/* code modified by LLM (iteration 2): Method body remains the same as it should verify correctly */
method Caller() {
  var x := F();
  var y := M();
}