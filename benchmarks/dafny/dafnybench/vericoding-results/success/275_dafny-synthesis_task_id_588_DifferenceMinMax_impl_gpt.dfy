// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}

// <vc-helpers>
lemma SlicesFactsLast(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures (a[..i+1])[|a[..i+1]|-1] == a[i]
  ensures (a[..i+1])[..|a[..i+1]|-1] == a[..i]
{
  assert |a[..i+1]| == i + 1;
  assert (a[..i+1])[|a[..i+1]|-1] == (a[..i+1])[i];
  assert (a[..i+1])[i] == a[i];
  assert (a[..i+1])[..|a[..i+1]|-1] == (a[..i+1])[..i];
  assert (a[..i+1])[..i] == a[..i];
}

lemma MinSnocArray(a: array<int>, i: int)
  requires 1 <= i < a.Length
  ensures Min(a[..i+1]) == (if a[i] <= Min(a[..i]) then a[i] else Min(a[..i]))
{
  reveal Min();
  SlicesFactsLast(a, i);
  assert |a[..i+1]| == i + 1;
  assert |a[..i+1]| > 1;
  calc {
    Min(a[..i+1]);
    ==
    (if (a[..i+1])[|a[..i+1]|-1] <= Min((a[..i+1])[..|a[..i+1]|-1])
     then (a[..i+1])[|a[..i+1]|-1] else Min((a[..i+1])[..|a[..i+1]|-1]));
    == {
      assert (a[..i+1])[|a[..i+1]|-1] == a[i];
      assert (a[..i+1])[..|a[..i+1]|-1] == a[..i];
    }
    (if a[i] <= Min(a[..i]) then a[i] else Min(a[..i]));
  }
}

lemma MaxSnocArray(a: array<int>, i: int)
  requires 1 <= i < a.Length
  ensures Max(a[..i+1]) == (if a[i] >= Max(a[..i]) then a[i] else Max(a[..i]))
{
  reveal Max();
  SlicesFactsLast(a, i);
  assert |a[..i+1]| == i + 1;
  assert |a[..i+1]| > 1;
  calc {
    Max(a[..i+1]);
    ==
    (if (a[..i+1])[|a[..i+1]|-1] >= Max((a[..i+1])[..|a[..i+1]|-1])
     then (a[..i+1])[|a[..i+1]|-1] else Max((a[..i+1])[..|a[..i+1]|-1]));
    == {
      assert (a[..i+1])[|a[..i+1]|-1] == a[i];
      assert (a[..i+1])[..|a[..i+1]|-1] == a[..i];
    }
    (if a[i] >= Max(a[..i]) then a[i] else Max(a[..i]));
  }
}
// </vc-helpers>

// <vc-spec>
method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var curMin := a[0];
  var curMax := a[0];
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant curMin == Min(a[..i])
    invariant curMax == Max(a[..i])
    decreases a.Length - i
  {
    MinSnocArray(a, i);
    MaxSnocArray(a, i);
    if a[i] <= curMin {
      curMin := a[i];
    }
    if a[i] >= curMax {
      curMax := a[i];
    }
    i := i + 1;
  }
  diff := Max(a[..]) - Min(a[..]);
}
// </vc-code>

