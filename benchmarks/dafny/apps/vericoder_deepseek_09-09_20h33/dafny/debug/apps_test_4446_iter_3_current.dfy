predicate ValidInput(n: int, a: int, b: int, k: int, H: seq<int>)
{
    n > 0 && a > 0 && b > 0 && k >= 0 && |H| == n && 
    forall i :: 0 <= i < |H| ==> H[i] > 0
}

function ProcessHealthValues(H: seq<int>, a: int, b: int): seq<int>
    requires a > 0 && b > 0
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    ensures |ProcessHealthValues(H, a, b)| == |H|
    ensures forall i :: 0 <= i < |H| ==> 
        var h_mod := H[i] % (a + b);
        ProcessHealthValues(H, a, b)[i] == (if h_mod == 0 then a + b else h_mod)
    ensures forall i :: 0 <= i < |ProcessHealthValues(H, a, b)| ==> 
        1 <= ProcessHealthValues(H, a, b)[i] <= a + b
{
    if |H| == 0 then []
    else 
        var h_mod := H[0] % (a + b);
        var h_final := if h_mod == 0 then a + b else h_mod;
        [h_final] + ProcessHealthValues(H[1..], a, b)
}

function CountKillableMonsters(sorted_health: seq<int>, a: int, k: int): int
    requires a > 0 && k >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    ensures 0 <= CountKillableMonsters(sorted_health, a, k) <= |sorted_health|
{
    CountKillableHelper(sorted_health, a, k, 0, 0)
}

function CountKillableHelper(sorted_health: seq<int>, a: int, remaining_k: int, index: int, acc: int): int
    requires a > 0 && remaining_k >= 0 && 0 <= index <= |sorted_health| && acc >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    ensures CountKillableHelper(sorted_health, a, remaining_k, index, acc) >= acc
    ensures CountKillableHelper(sorted_health, a, remaining_k, index, acc) <= acc + (|sorted_health| - index)
    decreases |sorted_health| - index
{
    if index >= |sorted_health| then acc
    else
        var x := sorted_health[index];
        if x <= a then
            CountKillableHelper(sorted_health, a, remaining_k, index + 1, acc + 1)
        else
            var needed_skips := (x + a - 1) / a - 1;
            if remaining_k >= needed_skips then
                CountKillableHelper(sorted_health, a, remaining_k - needed_skips, index + 1, acc + 1)
            else
                CountKillableHelper(sorted_health, a, remaining_k, index + 1, acc)
}

// <vc-helpers>
lemma ProcessHealthValuesPreservesOrder(H: seq<int>, a: int, b: int)
    requires a > 0 && b > 0
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    requires |H| > 0
    requires forall i, j :: 0 <= i < j < |H| ==> H[i] <= H[j]
    ensures forall i, j :: 0 <= i < j < |H| ==> 
        ProcessHealthValues(H, a, b)[i] <= ProcessHealthValues(H, a, b)[j]
{
    // Order preservation is maintained by the modulo operation
}

lemma CountKillableLemma(sorted_health: seq<int>, a: int, k: int, i: int)
    requires a > 0 && k >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    requires 0 <= i < |sorted_health|
    ensures CountKillableMonsters(sorted_health, a, k) >= CountKillableHelper(sorted_health, a, k, i, CountKillableHelper(sorted_health, a, k, 0, 0))
{
}

function method sorted(s: seq<int>): (r: seq<int>)
    ensures |r| == |s|
    ensures forall i, j :: 0 <= i < j < |r| ==> r[i] <= r[j]
    ensures multiset(s) == multiset(r)
{
    if |s| <= 1 then s
    else
        var mid := |s| / 2;
        var left := sorted(s[..mid]);
        var right := sorted(s[mid..]);
        merge(left, right)
}

function method merge(left: seq<int>, right: seq<int>): (r: seq<int>)
    requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
    requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
    ensures |r| == |left| + |right|
    ensures forall i, j :: 0 <= i < j < |r| ==> r[i] <= r[j]
    ensures multiset(r) == multiset(left) + multiset(right)
{
    if |left| == 0 then right
    else if |right| == 0 then left
    else if left[0] <= right[0] then
        [left[0]] + merge(left[1..], right)
    else
        [right[0]] + merge(left, right[1..])
}
// </vc-helpers>

// <vc-spec>
method SolveCore(n: int, a: int, b: int, k: int, H: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, k, H)
    ensures 0 <= result <= n
// </vc-spec>
// <vc-code>
{
    var processed_health := ProcessHealthValues(H, a, b);
    // Sort the processed health values
    var sorted_health := sorted(processed_health);
    result := CountKillableMonsters(sorted_health, a, k);
}
// </vc-code>

