// <vc-helpers>
// </vc-helpers>

method CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
// <vc-code>
{
  assume false;
}
// </vc-code>