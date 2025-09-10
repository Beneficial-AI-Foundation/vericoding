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
function Modulo(x: int, m: int): int
    requires m > 0
    ensures 0 <= Modulo(x, m) <= m - 1
{
    var r := x % m;
    if r < 0 then r + m else r
}

// Lemma to connect ProcessHealthValues logic directly to what we need
lemma NormalizeHealthValues(h: int, a: int, b: int)
    requires a > 0 && b > 0 && h > 0
    ensures var h_mod := h % (a + b);
            (if h_mod == 0 then a + b else h_mod) == (if Modulo(h, a + b) == 0 then a + b else Modulo(h, a + b))
{
    var h_mod := h % (a + b);
    var h_modulo := Modulo(h, a + b);
    if h_mod == 0 {
        assert (a+b) % (a+b) == 0;
        assert (a+b) == Modulo(a+b, a+b);
        assert (a+b) == (if Modulo(h, a+b) == 0 then a+b else Modulo(h,a+b));
    } else {
        assert h_mod == h_modulo;
    }
}

function sorted<T>(arr: seq<T>): seq<T> 
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] <= arr[j] || arr[j] <= arr[i] // Partial order
{
  if |arr| <= 1 then arr
  else 
    var pivot := arr[0];
    var less := sorted([x | x <- arr[1..], x < pivot]);
    var greater := sorted([x | x <- arr[1..], x >= pivot]);
    less + [pivot] + greater
}
// </vc-helpers>

// <vc-spec>
method SolveCore(n: int, a: int, b: int, k: int, H: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, k, H)
    ensures 0 <= result <= n
// </vc-spec>
// <vc-code>
{
    var processed_H := ProcessHealthValues(H, a, b);
    var sorted_H := sorted(processed_H);
    result := CountKillableMonsters(sorted_H, a, k);
}
// </vc-code>

