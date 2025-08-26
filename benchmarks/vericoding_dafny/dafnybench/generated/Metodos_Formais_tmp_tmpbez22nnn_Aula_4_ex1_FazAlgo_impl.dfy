// The method has:
// - Parameters: `a` and `b` (both integers)
// - Precondition: `a >= b && Par(a-b)` where `Par(n)` means `n % 2 == 0`
// - Returns: two integers `x` and `y`
//
// Since there are no postconditions specified, I just need to provide any implementation that doesn't violate the precondition. The simplest approach is to return some values for `x` and `y`.

predicate Par(n:int)
{
    n % 2 == 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
// </vc-spec>
// <vc-code>
{
  x := a;
  y := b;
}
// </vc-code>