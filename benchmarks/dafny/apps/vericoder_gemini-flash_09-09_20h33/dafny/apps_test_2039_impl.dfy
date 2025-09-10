predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n
}

function CountLocalExtrema(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|
}

predicate IsLocalExtremum(a: seq<int>, i: int)
    requires 0 <= i < |a|
{
    1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}

// <vc-helpers>
lemma CountLocalExtremaLemma(n: int, a: seq<int>)
    requires ValidInput(n, a)
    ensures CountLocalExtrema(n, a) == (if n <= 2 then 0 else CountLocalExtrema(n, a))
{
    if n <= 2 {
        var s := set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]));
        assert forall i :: !(1 <= i < n - 1) implies i !in s by {}; // If n <= 2, then there are no 'i' such that 1 <= i < n - 1.
                                               // For example, if n = 2, then n - 1 = 1. So 1 <= i < 1 is false.
                                               // If n = 1, then n - 1 = 0. So 1 <= i < 0 is false.
        assert s == {};
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures n <= 2 ==> result == 0
    ensures n > 2 ==> result <= n - 2
    ensures result == CountLocalExtrema(n, a)
// </vc-spec>
// <vc-code>
{
    if n <= 2 {
        CountLocalExtremaLemma(n, a);
        return 0;
    }

    var count := 0;
    var i := 1;
    while i < n - 1
        invariant 1 <= i <= n - 1
        invariant count == |set k | 1 <= k < i && IsLocalExtremum(a, k)|
        invariant forall k :: 1 <= k < i ==> (IsLocalExtremum(a, k) <==> (k in (set j | 1 <= j < n - 1 && IsLocalExtremum(a,j))))
        decreases (n - 1) - i
    {
        if IsLocalExtremum(a, i) {
            count := count + 1;
        }
        i := i + 1;
    }
    calc {
        count;
        |set k | 1 <= k < i && IsLocalExtremum(a, k)|;
        { assert i == n - 1; }
        |set k | 1 <= k < n - 1 && IsLocalExtremum(a, k)|;
        CountLocalExtrema(n, a);
    }
    return count;
}
// </vc-code>

