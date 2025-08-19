//IMPL 

//Second Exercise
method euclidianDiv(a: int,b : int) returns (q: int,r: int)
  requires a >= 0
  requires b > 0
  ensures a == b * q + r
  {
    q := 0;
    r := a;
    
    while r >= b
      invariant a == b * q + r
      invariant r >= 0
      decreases r
    {
      r := r - b;
      q := q + 1;
    }
  }