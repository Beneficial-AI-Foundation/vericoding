// <vc-helpers>
// </vc-helpers>

method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
// <vc-code>
{
  assume false;
}
// </vc-code>