predicate ValidInput(n: int, m: int, k: int, emotes: seq<int>)
{
    n >= 2 && k >= 1 && m >= 1 && |emotes| == n &&
    forall i :: 0 <= i < |emotes| ==> emotes[i] >= 1
}

function MaxHappiness(n: int, m: int, k: int, emotes: seq<int>): int
    requires ValidInput(n, m, k, emotes)
{
    var k_plus_1 := k + 1;
    var total := m / k_plus_1;
    var remainder := m % k_plus_1;
    // Assumes optimal strategy using highest and second highest values
    var max_val := MaxValue(emotes);
    var second_max_val := SecondMaxValue(emotes);
    remainder * max_val + max_val * (total * k) + second_max_val * total
}

function MaxValue(s: seq<int>): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures MaxValue(s) >= 1
    ensures exists i :: 0 <= i < |s| && s[i] == MaxValue(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxValue(s[1..]) then s[0]
    else MaxValue(s[1..])
}

function SecondMaxValue(s: seq<int>): int
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
{
    var max_val := MaxValue(s);
    var filtered := FilterOut(s, max_val, 1);
    if |filtered| > 0 then MaxValue(filtered) else 1
}

function FilterOut(s: seq<int>, val: int, count: int): seq<int>
    requires count >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures forall i :: 0 <= i < |FilterOut(s, val, count)| ==> FilterOut(s, val, count)[i] >= 1
{
    if |s| == 0 || count == 0 then s
    else if s[0] == val then FilterOut(s[1..], val, count - 1)
    else [s[0]] + FilterOut(s[1..], val, count)
}

// <vc-helpers>
lemma SecondMaxValue_at_least_one(s: seq<int>)
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures SecondMaxValue(s) >= 1
{
    var maxv := MaxValue(s);
    var filtered := FilterOut(s, maxv, 1);
    if |filtered| > 0 {
        assert SecondMaxValue(s) == MaxValue(filtered);
        assert MaxValue(filtered) >= 1;
    } else {
        assert SecondMaxValue(s) == 1;
    }
    assert SecondMaxValue(s) >= 1;
}

lemma MaxHappiness_nonneg(n: int, m: int, k: int, emotes: seq<int>)
    requires ValidInput(n, m, k, emotes)
    ensures MaxHappiness(n, m, k, emotes) >= 0
{
    var k_plus_1 := k + 1;
    var total := m / k_plus_1;
    var remainder := m % k_plus_1;
    var maxv := MaxValue(emotes);
    var second := SecondMaxValue(emotes);

    // maxv >= 1 by MaxValue's ensures
    assert maxv >= 1;

    // second >= 1 by lemma about SecondMaxValue
    SecondMaxValue_at_least_one(emotes);
    assert second >= 1;

    // k_plus_1 > 0, so division and modulo yield non-negative results
    assert k_plus_1 > 0;
    assert total >= 0;
    assert remainder >= 0;

    // sum of non-negatives is non-negative
    assert remainder * maxv + maxv * (total * k) + second * total >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, emotes: seq<int>) returns (result: int)
    requires ValidInput(n, m, k, emotes)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := MaxHappiness(n, m, k, emotes);
  MaxHappiness_nonneg(n, m, k, emotes);
}
// </vc-code>

