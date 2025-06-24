//IMPL 

method Fact(x: int) returns (y: int)
  requires x >= 0;   
{
  if x == 0 {
    y := 1;
  } else {
    y := 1;
    var i := 1;
    while i <= x
      invariant 1 <= i <= x + 1
      invariant y == factorial_helper(i - 1)
    {
      y := y * i;
      i := i + 1;
    }
  }
}

function factorial_helper(n: int): int
  requires n >= 0
{
  if n == 0 then 1 else n * factorial_helper(n - 1)
}

//ATOM_PLACEHOLDER_Main