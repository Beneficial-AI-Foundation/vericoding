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
lemma sum_trips_step(w: seq<int>, k: int)
    requires k > 0
    requires |w| > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    ensures sum_trips(w, k) == (w[0] + k - 1) / k + sum_trips(w[1..], k)
{
    // This follows directly from the definition of sum_trips
}

lemma sum_trips_prefix(w: seq<int>, k: int, i: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= i < |w|
    ensures w[..i+1] == w[..i] + [w[i]]
    ensures sum_trips(w[..i+1], k) == sum_trips(w[..i], k) + (w[i] + k - 1) / k
{
    assert w[..i+1] == w[..i] + [w[i]];
    var prefix := w[..i];
    var extended := w[..i+1];
    assert extended == prefix + [w[i]];
    
    sum_trips_append_single(prefix, w[i], k);
}

lemma sum_trips_append_single(w: seq<int>, x: int, k: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires x >= 0
    ensures sum_trips(w + [x], k) == sum_trips(w, k) + (x + k - 1) / k
{
    if |w| == 0 {
        assert w + [x] == [x];
        calc {
            sum_trips([x], k);
        == 
            (x + k - 1) / k + sum_trips([], k);
        == 
            (x + k - 1) / k + 0;
        ==
            sum_trips([], k) + (x + k - 1) / k;
        }
    } else {
        calc {
            sum_trips(w + [x], k);
        == { assert (w + [x])[0] == w[0]; assert (w + [x])[1..] == w[1..] + [x]; }
            (w[0] + k - 1) / k + sum_trips(w[1..] + [x], k);
        == { sum_trips_append_single(w[1..], x, k); }
            (w[0] + k - 1) / k + sum_trips(w[1..], k) + (x + k - 1) / k;
        == // By definition of sum_trips for |w| > 0
            sum_trips(w, k) + (x + k - 1) / k;
        }
    }
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
        assert sum_trips([], k) == 0;
    } else if i == |w| {
        assert w[..|w|] == w;
        assert w[|w|..] == [];
        assert sum_trips([], k) == 0;
    } else {
        sum_trips_split(w, k, i);
    }
}

lemma sum_trips_split(w: seq<int>, k: int, i: int)
    requires k > 0
    requires forall j :: 0 <= j < |w| ==> w[j] >= 0
    requires 0 <= i <= |w|
    ensures sum_trips(w[..i], k) + sum_trips(w[i..], k) == sum_trips(w, k)
{
    if i == 0 {
        assert w[..0] == [];
        assert w[0..] == w;
    } else if i == |w| {
        assert w[..i] == w;
        assert w[i..] == [];
    } else if |w| == 0 {
        assert w[..i] == [];
        assert w[i..] == [];
    } else {
        if i == 1 {
            assert w[..1] == [w[0]];
            assert w[1..] == w[1..];
            calc {
                sum_trips(w[..1], k) + sum_trips(w[1..], k);
            ==
                sum_trips([w[0]], k) + sum_trips(w[1..], k);
            ==
                ((w[0] + k - 1) / k + sum_trips([], k)) + sum_trips(w[1..], k);
            ==
                (w[0] + k - 1) / k + 0 + sum_trips(w[1..], k);
            ==
                (w[0] + k - 1) / k + sum_trips(w[1..], k);
            == // By definition of sum_trips for |w| > 0
                sum_trips(w, k);
            }
        } else {
            calc {
                sum_trips(w[..i], k) + sum_trips(w[i..], k);
            == { assert w[..i][0] == w[0]; assert w[..i][1..] == w[1..i]; }
                (w[0] + k - 1) / k + sum_trips(w[1..i], k) + sum_trips(w[i..], k);
            == { sum_trips_split(w[1..], k, i-1); }
                (w[0] + k - 1) / k + sum_trips(w[1..], k);
            == // By definition of sum_trips for |w| > 0
                sum_trips(w, k);
            }
        }
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
        var prev_i := i;
        total := total + (w[i] + k - 1) / k;
        
        // Help the verifier understand the invariant is maintained
        sum_trips_prefix(w, k, i);
        assert w[..i+1] == w[..i] + [w[i]];
        assert total == sum_trips(w[..i], k) + (w[i] + k - 1) / k;
        assert total == sum_trips(w[..i+1], k);
        
        i := i + 1;
        assert w[..i] == w[..prev_i+1];
    }
    
    assert i == |w|;
    assert w[..i] == w;
    assert total == sum_trips(w, k);
    
    result := (total + 1) / 2;
}
// </vc-code>

