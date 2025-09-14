

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
// </vc-spec>
// <vc-code>
{
    var s := set i | i in numbers && i < threshold;
    count := |s|;
}
// </vc-code>

