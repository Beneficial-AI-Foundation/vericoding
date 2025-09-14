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

// </vc-helpers>

// <vc-spec>
method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var m := a[0];
  var M := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant m == Min(a[..i])
    invariant M == Max(a[..i])
    decreases n - i
  {
    assert |a[..i+1]| == i + 1;
    assert (a[..i+1])[..i] == a[..i];
    assert (a[..i+1])[i] == a[i];

    var x := a[i];
    var mp := m;
    var Mp := M;

    if x <= mp {
      m := x;
    } else {
      m := mp;
    }

    if x >= Mp {
      M := x;
    } else {
      M := Mp;
    }

    assert m == (if x <= mp then x else mp);
    assert M == (if x >= Mp then x else Mp);

    assert mp == Min(a[..i]);
    assert Mp == Max(a[..i]);

    assert Min(a[..i+1]) == (if a[i] <= Min(a[..i]) then a[i] else Min(a[..i]));
    assert Max(a[..i+1]) == (if a[i] >= Max(a[..i]) then a[i] else Max(a[..i]));

    i := i + 1;
  }
  assert i >= n && i <= n;
  assert i == n;
  assert n == a.Length;
  assert i == a.Length;
  assert a[..i] == a[..];
  assert m == Min(a[..]);
  assert M == Max(a[..]);
  sum := M + m;
}
// </vc-code>

