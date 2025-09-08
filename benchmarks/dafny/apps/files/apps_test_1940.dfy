Given n types of pebbles with w_i pebbles of type i, and a person with 2 pockets 
that can each hold at most k pebbles, find the minimum number of days needed to 
collect all pebbles. Different pebble types cannot be mixed in the same pocket, 
both pockets can be used simultaneously on the same day, and each pebble type 
must be collected completely.

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

lemma sum_trips_append_lemma(w: seq<int>, elem: int, k: int)
    requires k > 0
    requires forall i :: 0 <= i < |w| ==> w[i] >= 0
    requires elem >= 0
    ensures sum_trips(w + [elem], k) == sum_trips(w, k) + (elem + k - 1) / k
{
    if |w| == 0 {
        assert w + [elem] == [elem];
        assert sum_trips([elem], k) == (elem + k - 1) / k;
        assert sum_trips(w, k) == 0;
    } else {
        assert (w + [elem])[0] == w[0];
        assert (w + [elem])[1..] == w[1..] + [elem];
        sum_trips_append_lemma(w[1..], elem, k);
        assert sum_trips(w[1..] + [elem], k) == sum_trips(w[1..], k) + (elem + k - 1) / k;
        assert sum_trips(w + [elem], k) == (w[0] + k - 1) / k + sum_trips(w[1..] + [elem], k);
        assert sum_trips(w + [elem], k) == (w[0] + k - 1) / k + sum_trips(w[1..], k) + (elem + k - 1) / k;
        assert sum_trips(w, k) == (w[0] + k - 1) / k + sum_trips(w[1..], k);
    }
}

method solve(n: int, k: int, w: seq<int>) returns (result: int)
    requires ValidInput(n, k, w)
    ensures result >= 0
    ensures result == (sum_trips(w, k) + 1) / 2
{
    var tot := 0;

    var i := 0;
    while i < |w|
        invariant 0 <= i <= |w|
        invariant tot >= 0
        invariant tot == sum_trips(w[..i], k)
    {
        var trips := (w[i] + k - 1) / k;
        sum_trips_append_lemma(w[..i], w[i], k);
        assert w[..i] + [w[i]] == w[..i+1];
        tot := tot + trips;
        i := i + 1;
    }

    assert i == |w|;
    assert w[..i] == w;
    assert tot == sum_trips(w, k);
    result := (tot + 1) / 2;
}
