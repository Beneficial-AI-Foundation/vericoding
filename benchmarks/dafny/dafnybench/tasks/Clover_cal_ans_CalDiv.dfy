// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
