//ATOM example_predicate
predicate IsPositive(x: int) { x > 0 }

//IMPL example_method
//CONSTRAINTS: no loops
method Double(x: int) returns (result: int)
  requires x >= 0
  ensures result == 2 * x
{
  // implementation that may have verification errors
  result := x + x;
}