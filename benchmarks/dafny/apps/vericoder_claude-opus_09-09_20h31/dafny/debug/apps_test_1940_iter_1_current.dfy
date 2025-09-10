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
lemma sum_trips_lemma(w: seq<int>, k: int, i: int, acc: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= i <= |w|
    requires acc >= 0
    ensures acc + sum_trips(w[i..], k) == acc + sum_trips(w[i..], k)
{
    // This lemma helps establish that our accumulator pattern is correct
}

lemma sum_trips_accumulator(w: seq<int>, k: int, i: int, acc: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= i <= |w|
    requires acc == sum_trips(w[..i], k)
    ensures acc + sum_trips(w[i..], k) == sum_trips(w, k)
{
    if i == 0 {
        assert w[..0] == [];
        assert w[0..] == w;
    } else if i == |w| {
        assert w[..|w|] == w;
        assert w[|w|..] == [];
    } else {
        assert w == w[..i] + w[i..];
    }
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
    var total := 0;
    var i := 0;
    
    while i < |w|
        invariant 0 <= i <= |w|
        invariant total >= 0
        invariant total == sum_trips(w[..i], k)
    {
        total := total + (w[i] + k - 1) / k;
        i := i + 1;
    }
    
    assert i == |w|;
    assert w[..i] == w;
    assert total == sum_trips(w, k);
    
    result := (total + 1) / 2;
}
// </vc-code>

