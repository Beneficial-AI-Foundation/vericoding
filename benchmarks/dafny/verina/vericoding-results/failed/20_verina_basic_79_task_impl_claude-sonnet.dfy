// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to avoid termination issues */
function MaxInPrefix(a: array<int>, len: int): int
    requires 0 < len <= a.Length
    reads a
    decreases len
{
    if len == 1 then a[0]
    else
        var prev_max := MaxInPrefix(a, len - 1);
        if a[len - 1] > prev_max then a[len - 1] else prev_max
}

predicate MaxExists(a: array<int>, start: int, end: int, max_val: int)
    requires 0 <= start < end <= a.Length
    reads a
{
    exists i :: start <= i < end && a[i] == max_val
}

predicate AllLeq(a: array<int>, start: int, end: int, max_val: int)
    requires 0 <= start <= end <= a.Length
    reads a
{
    forall i :: start <= i < end ==> a[i] <= max_val
}
// </vc-helpers>

// <vc-spec>
method OnlineMax(a: array<int>, x: int) returns (result: (int, int))
    requires
        a.Length > 0 &&
        x < a.Length
    ensures
        var (m, p) := result;
        x <= p && p < a.Length &&
        (forall i :: 0 <= i < x ==> a[i] <= m) &&
        (exists i :: 0 <= i < x && a[i] == m) &&
        ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
        ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix loop invariant initialization */
    var max_val := a[0];
    var i := 1;
    
    while i < x
        invariant 1 <= i <= x
        invariant forall j :: 0 <= j < i ==> a[j] <= max_val
        invariant exists j :: 0 <= j < i && a[j] == max_val
    {
        if a[i] > max_val {
            max_val := a[i];
        }
        i := i + 1;
    }
    
    if x == 0 {
        max_val := a[0];
    }
    
    var p := x;
    while p < a.Length
        invariant x <= p <= a.Length
        invariant forall j :: x <= j < p ==> a[j] <= max_val
    {
        if a[p] > max_val {
            result := (max_val, p);
            return;
        }
        p := p + 1;
    }
    
    result := (max_val, a.Length - 1);
}
// </vc-code>
