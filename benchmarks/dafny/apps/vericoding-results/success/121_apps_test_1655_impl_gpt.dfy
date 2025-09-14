predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < n ==> a[i] >= 0
}

function CountSurvivors(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    CountSurvivorsFrom(n, a, 0, n)
}

function CountSurvivorsFrom(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + CountSurvivorsFrom(n, a, start + 1, newLeft)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result <= n
    ensures result == CountSurvivors(n, a)
// </vc-spec>
// <vc-code>
{
  var start := 0;
  var left := n;
  var res := 0;
  while start < n
    invariant ValidInput(n, a)
    invariant 0 <= start <= n
    invariant left <= n
    invariant res >= 0
    invariant res <= start
    invariant res + CountSurvivorsFrom(n, a, start, left) == CountSurvivors(n, a)
    decreases n - start
  {
    assert CountSurvivorsFrom(n, a, start, left) ==
      (if start >= n then 0
       else
         (if (n - 1 - start) < left then 1 else 0) +
         CountSurvivorsFrom(n, a, start + 1,
           (if (n - 1 - start) - a[n - 1 - start] < left then (n - 1 - start) - a[n - 1 - start] else left)));

    var i := n - 1 - start;
    var survives := if i < left then 1 else 0;
    var newLeft := if i - a[i] < left then i - a[i] else left;

    assert 0 <= i < n;
    assert a[i] >= 0;
    assert i - a[i] <= i;
    assert i <= n - 1;
    assert i - a[i] <= n;

    assert 0 <= survives;
    assert survives <= 1;

    res := res + survives;
    start := start + 1;
    left := newLeft;
  }
  assert start == n;
  assert CountSurvivorsFrom(n, a, start, left) == 0;
  result := res;
}
// </vc-code>

