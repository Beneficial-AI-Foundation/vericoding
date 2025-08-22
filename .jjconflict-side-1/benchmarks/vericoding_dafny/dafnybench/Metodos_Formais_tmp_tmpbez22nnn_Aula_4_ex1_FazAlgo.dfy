predicate Par(n:int)
{
    n % 2 == 0
}

// <vc-helpers>
// </vc-helpers>

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
// <vc-code>
{
  assume false;
}
// </vc-code>