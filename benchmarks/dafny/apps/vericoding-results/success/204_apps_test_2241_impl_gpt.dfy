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
lemma unfold_sum_nonempty(a: seq<int>, b: seq<int>)
  requires |a| == |b| && |a| > 0
  ensures sum_contributions(a, b) ==
    (if b[0] > 1 && 2 * a[0] >= b[0]
     then (b[0] / 2) * (b[0] - (b[0] / 2))
     else -1) + sum_contributions(a[1..], b[1..])
{}

lemma sum_contributions_empty(a: seq<int>, b: seq<int>)
  requires |a| == |b| && |a| == 0
  ensures sum_contributions(a, b) == 0
{}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var acc := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
    invariant acc + sum_contributions(a[i..], b[i..]) == sum_contributions(a, b)
    decreases |a| - i
  {
    var x := b[i] / 2;
    var y := b[i] - x;
    var c := if b[i] > 1 && 2 * a[i] >= b[i] then x * y else -1;
    var acc0 := acc;
    acc := acc + c;
    var i1 := i + 1;

    assert |a[i..]| == |b[i..]|;
    assert i < |a|;

    assert c == (if b[i] > 1 && 2 * a[i] >= b[i]
                 then (b[i] / 2) * (b[i] - (b[i] / 2))
                 else -1);

    calc {
      acc + sum_contributions(a[i1..], b[i1..]);
      == { assert acc == acc0 + c; }
      (acc0 + c) + sum_contributions(a[i1..], b[i1..]);
      == { unfold_sum_nonempty(a[i..], b[i..]); }
      acc0 + sum_contributions(a[i..], b[i..]);
      == { }
      sum_contributions(a, b);
    }

    assert 0 <= i1 <= |a|;
    i := i1;
  }

  assert i == |a|;
  assert |a[i..]| == |b[i..]|;
  assert |a[i..]| == 0;
  sum_contributions_empty(a[i..], b[i..]);
  assert sum_contributions(a[i..], b[i..]) == 0;

  result := acc;
}
// </vc-code>

