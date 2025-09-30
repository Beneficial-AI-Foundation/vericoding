

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
// </vc-spec>
// <vc-code>
{
  x := 191 / 7;
  y := 191 % 7;
}
// </vc-code>

