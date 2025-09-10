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
lemma sum_trips_non_decreasing(w: seq<int>, k: int, i: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= i < |w|
    ensures sum_trips(w, k) <= sum_trips(w[i..], k) + sum_trips(w[0..i], k)
{
    sum_trips_split_lemma(w, k, i);
}

lemma sum_trips_split_lemma(w: seq<int>, k: int, i: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= i <= |w|
    ensures sum_trips(w, k) == sum_trips(w[0..i], k) + sum_trips(w[i..], k)
{
    if |w| == 0 {
    } else if i == 0 {
        assert w[0..0] == [];
        assert w[0..] == w;
    } else if i == |w| {
        assert w[|w|..] == [];
        assert w[0..|w|] == w;
    } else {
        calc {
            sum_trips(w, k);
            (w[0] + k - 1) / k + sum_trips(w[1..], k);
            { sum_trips_split_lemma(w[1..], k, i-1); }
            (w[0] + k - 1) / k + (sum_trips(w[1..i], k) + sum_trips(w[i..], k));
            sum_trips(w[0..i], k) + sum_trips(w[i..], k);
        }
    }
}

lemma sum_trips_subsequence(w: seq<int>, k: int, left: int, right: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= left <= right < |w|
    ensures sum_trips(w[left..right+1], k) >= 0
{
}

lemma sum_trips_decreases(w: seq<int>, k: int, left: int, right: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= left <= right < |w|
    ensures sum_trips(w[left..right+1], k) == (w[left] + k - 1) / k + sum_trips(w[left+1..right+1], k)
    ensures sum_trips(w[left..right+1], k) == sum_trips(w[left..right], k) + (w[right] + k - 1) / k
{
    var s := w[left..right+1];
    if |s| > 0 {
        assert sum_trips(s, k) == (s[0] + k - 1) / k + sum_trips(s[1..], k);
        assert s[0] == w[left];
        assert s[1..] == w[left+1..right+1];
    }
    if |s| > 1 {
        var s' := w[left..right];
        assert sum_trips(s, k) == sum_trips(s', k) + (s[|s|-1] + k - 1) / k;
        assert s[|s|-1] == w[right];
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, w: seq<int>) returns (result: int)
    requires ValidInput(n, k, w)
    ensures result >= 0
    ensures result == (sum_trips(w, k) + 1) / 2
// </vc-spec>
// <vc-code>
{
    var total_trips := sum_trips(w, k);
    var remaining_trips := total_trips;
    var left := 0;
    var right := n - 1;
    result := 0;
    
    while (remaining_trips > 0)
        invariant 0 <= left <= right + 1 <= n
        invariant remaining_trips == sum_trips(w[left..right + 1], k)
        invariant result == (total_trips - remaining_trips) / 2
        decreases right - left + 1
    {
        var left_trip := (w[left] + k - 1) / k;
        var right_trip := (w[right] + k - 1) / k;
        
        sum_trips_decreases(w, k, left, right);
        
        if left_trip <= remaining_trips && left_trip <= right_trip {
            remaining_trips := remaining_trips - left_trip;
            left := left + 1;
            result := result + 1;
        } else if right_trip <= remaining_trips {
            remaining_trips := remaining_trips - right_trip;
            right := right - 1;
            result := result + 1;
        } else {
            // This case should not happen but helps with verification
            break;
        }
    }
    assert remaining_trips == 0;
    assert result == total_trips / 2;
}
// </vc-code>

