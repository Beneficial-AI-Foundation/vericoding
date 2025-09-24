// <vc-preamble>
predicate ValidInput(n: int, h: int, segments: seq<(int, int)>)
{
    n >= 1 &&
    h >= 1 &&
    |segments| == n &&
    (forall i :: 0 <= i < |segments| ==> segments[i].0 >= 1 && segments[i].0 < segments[i].1 <= 1000000000) &&
    (forall i :: 0 <= i < |segments| - 1 ==> segments[i].1 <= segments[i+1].0)
}

function compute_gap_sum(segments: seq<(int, int)>, pos: int): int
    requires |segments| >= 1
    requires 0 <= pos < |segments|
    requires forall i :: 0 <= i < |segments| - 1 ==> segments[i].1 <= segments[i+1].0
{
    if pos == 0 then 0
    else compute_gap_sum(segments, pos - 1) + segments[pos].0 - segments[pos - 1].1
}

function compute_airflow_sum(segments: seq<(int, int)>, pos: int): int
    requires |segments| >= 1
    requires 0 <= pos < |segments|
{
    if pos == 0 then segments[0].1 - segments[0].0
    else compute_airflow_sum(segments, pos - 1) + segments[pos].1 - segments[pos].0
}
// </vc-preamble>

// <vc-helpers>
lemma gap_sum_monotonic(segments: seq<(int, int)>, i: int, j: int)
    requires |segments| >= 1
    requires 0 <= i < j < |segments|
    requires forall k :: 0 <= k < |segments| - 1 ==> segments[k].1 <= segments[k+1].0
    ensures compute_gap_sum(segments, i) <= compute_gap_sum(segments, j)
    decreases j - i
{
    if j == i + 1 {
        assert compute_gap_sum(segments, j) == compute_gap_sum(segments, i) + segments[j].0 - segments[j-1].1;
        assert segments[j-1].1 <= segments[j].0;
    } else {
        gap_sum_monotonic(segments, i, j-1);
        gap_sum_monotonic(segments, j-1, j);
    }
}

method bisect_left(arr: array<int>, n: int, target: int) returns (pos: int)
    requires arr.Length >= n >= 0
    requires forall i, j :: 0 <= i < j < n ==> arr[i] <= arr[j]
    ensures 0 <= pos <= n
    ensures pos == 0 || (pos > 0 && arr[pos-1] < target)
    ensures pos == n || arr[pos] >= target
{
    var left := 0;
    var right := n;

    while left < right
        invariant 0 <= left <= right <= n
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        invariant forall i :: right <= i < n ==> arr[i] >= target
    {
        var mid := left + (right - left) / 2;
        if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }

    pos := left;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, h: int, segments: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, h, segments)
    ensures result >= h
    ensures n == 1 ==> result == h + segments[0].1 - segments[0].0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        result := h + segments[0].1 - segments[0].0;
        return;
    }

    var gap_sum := new int[n];
    var airflow_sum := new int[n];

    gap_sum[0] := 0;
    airflow_sum[0] := segments[0].1 - segments[0].0;

    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> gap_sum[j] == compute_gap_sum(segments, j)
        invariant forall j :: 0 <= j < i ==> airflow_sum[j] == compute_airflow_sum(segments, j)
        invariant forall j, k :: 0 <= j < k < i ==> gap_sum[j] <= gap_sum[k]
    {
        gap_sum[i] := gap_sum[i-1] + segments[i].0 - segments[i-1].1;
        airflow_sum[i] := airflow_sum[i-1] + segments[i].1 - segments[i].0;
        i := i + 1;
    }

    var ans := h;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant ans >= h
        invariant forall j, k :: 0 <= j < k < n ==> gap_sum[j] <= gap_sum[k]
    {
        var target := h + gap_sum[i];
        var cnt := bisect_left(gap_sum, n, target);

        var res: int;
        if i == 0 {
            if cnt > 0 {
                res := airflow_sum[cnt-1] + h - gap_sum[cnt-1];
            } else {
                res := h;
            }
        } else {
            if cnt > 0 {
                res := airflow_sum[cnt-1] - (airflow_sum[i-1] + gap_sum[i] - gap_sum[i-1]) + h - (gap_sum[cnt-1] - gap_sum[i]);
            } else {
                res := h;
            }
        }

        if res > ans {
            ans := res;
        }
        i := i + 1;
    }

    result := ans;
}
// </vc-code>
