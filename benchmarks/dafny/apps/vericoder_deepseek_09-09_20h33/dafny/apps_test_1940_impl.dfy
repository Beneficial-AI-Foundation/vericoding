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
    if i == 0 {
        assert w[0..0] == [];
        assert w[0..] == w;
    } else if i == |w| {
        assert w[|w|..] == [];
        assert w[0..|w|] == w;
    } else if |w| > 0 {
        calc == {
            sum_trips(w, k);
            (w[0] + k - 1) / k + sum_trips(w[1..], k);
            { sum_trips_split_lemma(w[1..], k, i-1); }
            (w[0] + k - 1) / k + (sum_trips(w[1..i], k) + sum_trips(w[i..], k));
            { 
                assert w[0..i] == [w[0]] + w[1..i];
                assert sum_trips(w[0..i], k) == (w[0] + k - 1) / k + sum_trips(w[1..i], k);
            }
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
{
    var s := w[left..right+1];
    if |s| > 0 {
        assert s[0] == w[left];
        assert s[1..] == w[left+1..right+1];
    }
}

lemma sum_trips_decreases_right(w: seq<int>, k: int, left: int, right: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= left <= right < |w|
    ensures sum_trips(w[left..right+1], k) == sum_trips(w[left..right], k) + (w[right] + k - 1) / k
{
    if right > left {
        var s := w[left..right];
        sum_trips_split_lemma(w[left..right+1], k, right - left);
        assert w[left..right] == w[left..right+1][0..right-left];
        assert [w[right]] == w[left..right+1][right-left..];
    } else if right == left {
        assert w[left..right+1] == [w[left]];
        assert w[left..right] == [];
        assert sum_trips([w[left]], k) == (w[left] + k - 1) / k;
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
    var total_trips := sum_trips(w, k);
    var remaining_trips := total_trips;
    var left := 0;
    var right := n - 1;
    result := 0;
    
    while (remaining_trips > 0 && left <= right)
        invariant 0 <= left <= right + 1 <= n
        invariant remaining_trips == sum_trips(w[left..right + 1], k)
        invariant result == (total_trips - remaining_trips) / 2
        decreases right - left
    {
        var left_trip := (w[left] + k - 1) / k;
        var right_trip := (w[right] + k - 1) / k;
        
        if left_trip <= remaining_trips && left_trip <= right_trip {
            sum_trips_decreases(w, k, left, right);
            remaining_trips := remaining_trips - left_trip;
            left := left + 1;
            result := result + 1;
        } else if right_trip <= remaining_trips {
            sum_trips_decreases_right(w, k, left, right);
            remaining_trips := remaining_trips - right_trip;
            right := right - 1;
            result := result + 1;
        } else {
            break;
        }
    }
    
    assert remaining_trips == 0 || left > right;
    
    if total_trips % 2 == 0 {
        assert result == total_trips / 2;
        assert (total_trips + 1) / 2 == total_trips / 2;
    } else {
        if result == total_trips / 2 {
            result := result + 1;
        }
    }
}
// </vc-code>

