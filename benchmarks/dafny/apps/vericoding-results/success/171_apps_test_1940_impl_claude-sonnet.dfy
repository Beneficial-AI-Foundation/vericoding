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
lemma SumTripsNonNegative(w: seq<int>, k: int)
    requires k > 0
    requires forall i :: 0 <= i < |w| ==> w[i] >= 0
    ensures sum_trips(w, k) >= 0
{
    if |w| == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        assert w[0] >= 0;
        assert (w[0] + k - 1) / k >= 0;
        SumTripsNonNegative(w[1..], k);
        assert sum_trips(w[1..], k) >= 0;
    }
}

lemma DivisionByTwoNonNegative(x: int)
    requires x >= 0
    ensures (x + 1) / 2 >= 0
{
    // For any non-negative x, (x + 1) / 2 >= 0
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
    SumTripsNonNegative(w, k);
    var total := sum_trips(w, k);
    DivisionByTwoNonNegative(total);
    result := (total + 1) / 2;
}
// </vc-code>

