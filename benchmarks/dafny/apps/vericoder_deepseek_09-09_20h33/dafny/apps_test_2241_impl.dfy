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
lemma sum_contributions_step(a: seq<int>, b: seq<int>)
  requires |a| == |b|
  requires |a| > 0
  ensures sum_contributions(a, b) == 
    (if b[0] > 1 && 2 * a[0] >= b[0] then
        var x := b[0] / 2;
        var y := b[0] - x;
        x * y
     else -1) + sum_contributions(a[1..], b[1..])
{
  // This lemma is automatically proven by Dafny as it matches the function definition
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    result := 0;
  } else {
    var head_contribution := -1;
    if b[0] > 1 && 2 * a[0] >= b[0] {
      var x := b[0] / 2;
      var y := b[0] - x;
      head_contribution := x * y;
    }
    var tail_result := solve(a[1..], b[1..]);
    result := head_contribution + tail_result;
  }
}
// </vc-code>

