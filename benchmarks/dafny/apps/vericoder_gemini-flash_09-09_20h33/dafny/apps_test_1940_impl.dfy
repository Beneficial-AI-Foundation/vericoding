predicate ValidInput(n: int, k: int, w: seq<int>)
{
    k > 0 && n >= 0 && |w| == n && forall i :: 0 <= i < |w| ==> w[i] >= 0
}

function sum_trips(w: seq<int>, k: int): int
    requires k > 0
    requires forall i :: 0 <= i < |w| ==> w[i] >= 0
    ensures sum_trips(w, k) >= 0
{
    if |w| == 0 then 0
    else (w[0] + k - 1) / k + sum_trips(w[1..], k)
}

// <vc-helpers>
function sum_trips_iterative(w: seq<int>, k: int): int
    requires k > 0
    requires forall i :: 0 <= i < |w| ==> w[i] >= 0
    ensures sum_trips_iterative(w, k) == sum_trips(w, k)
{
    var s := 0;
    var i := 0;
    while i < |w|
        invariant 0 <= i <= |w|
        invariant s == sum_trips(w[..i], k)
    {
        s := s + (w[i] + k - 1) / k;
        i := i + 1;
    }
    return s;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, w: seq<int>) returns (result: int)
    requires ValidInput(n, k, w)
    ensures result >= 0
    ensures result == (sum_trips(w, k) + 1) / 2
// </vc-spec>
// <vc-code>
{
    var s := 0;
    if n == 0 {
        return 0;
    }

    s := sum_trips_iterative(w, k);
    assert s == sum_trips(w, k);

    result := (s + 1) / 2;
    return result;
}
// </vc-code>

