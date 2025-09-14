function sum_contributions(a: seq<int>, b: seq<int>): int
    requires |a| == |b|
{
    if |a| == 0 then 0
    else 
        (if b[0] > 1 && 2 * a[0] >= b[0] then
            var x := b[0] / 2;
            var y := b[0] - x;
            x * y
         else -1) + sum_contributions(a[1..], b[1..])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
    invariant result + sum_contributions(a[i..], b[i..]) == sum_contributions(a, b)
    decreases |a| - i
  {
    if b[i] > 1 && 2 * a[i] >= b[i] {
      var x := b[i] / 2;
      var y := b[i] - x;
      result := result + (x * y);
    } else {
      result := result - 1;
    }
    i := i + 1;
  }
}
// </vc-code>

