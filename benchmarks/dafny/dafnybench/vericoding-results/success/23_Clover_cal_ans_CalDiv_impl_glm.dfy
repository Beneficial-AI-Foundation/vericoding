

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
// </vc-spec>
// <vc-code>
{
  x, y := 191 / 7, 191 % 7;
}
// </vc-code>

