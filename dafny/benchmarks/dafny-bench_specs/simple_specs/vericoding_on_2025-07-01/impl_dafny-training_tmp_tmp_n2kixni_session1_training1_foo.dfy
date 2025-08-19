//ATOM

method abs(x: int) returns (y: int)
  ensures true
{
  y := 0;
  assume true;
  return y;
}

/** Call abs */


// SPEC
method foo(x: int) 
  requires x >= 0
{
}

/**
 * Example 0.b.
 * The goal is to compute the maximum of x and y and return it in m.
 * The current version is buggy and returns 0 is x > y and 1 if x <= 1.
 * 
 * Try to:
 * 1. write the post-condition that shows that max(x,y) (i.e. m) is larger than x and y.
 * 2. write a set of post-conditions that fully characterises max.
 * 3. fix the code and make sure it verifies.
 */