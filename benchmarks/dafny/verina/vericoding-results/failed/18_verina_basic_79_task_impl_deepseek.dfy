// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Strengthened loop invariants and fixed termination */
lemma MaxLemma(a: array<int>, x: int, m: int, p: int)
    requires a.Length > 0 && x < a.Length
    requires x <= p && p < a.Length
    requires forall i :: 0 <= i < x ==> a[i] <= m
    requires exists i :: 0 <= i < x && a[i] == m
    ensures (p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)
    ensures (forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1
{
    if p < a.Length - 1 {
        var found := false;
        var k := x;
        while k <= p
            invariant x <= k <= p + 1
            invariant !found ==> forall j :: x <= j < k ==> a[j] <= m
            invariant found ==> exists j :: x <= j < k && a[j] > m
        {
            if a[k] > m {
                found := true;
            }
            k := k + 1;
        }
        if !found {
            assert a[p] > m;
        }
    }
    if forall i :: x <= i < a.Length ==> a[i] <= m {
        assert p == a.Length - 1;
    }
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
    /* code modified by LLM (iteration 5): Fixed loop invariants ensuring valid array bounds */
    var m := a[0];
    var p := 0;
    
    var i := 1;
    while i < x
        invariant 0 <= p < a.Length
        invariant 0 <= i <= x
        invariant forall j :: 0 <= j < i ==> a[j] <= m
        invariant exists j :: 0 <= j < i && a[j] == m
    {
        if a[i] > m {
            m := a[i];
            p := i;
        }
        i := i + 1;
    }
    
    i := x;
    while i < a.Length
        invariant x <= p < a.Length
        invariant x <= i <= a.Length
        invariant forall j :: 0 <= j < x ==> a[j] <= m
        invariant exists j :: 0 <= j < x && a[j] == m
        invariant forall j :: x <= j < i ==> a[j] <= m
    {
        if a[i] > m {
            m := a[i];
            p := i;
        }
        i := i + 1;
    }
    
    MaxLemma(a, x, m, p);
    result := (m, p);
}
// </vc-code>
