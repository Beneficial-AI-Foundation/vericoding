predicate ValidInput(n: int, s: string)
{
    n >= 1 && n <= 2000 && |s| == n && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(result: string, n: int)
{
    |result| == n && 
    forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
}

predicate PreservesCharacters(s: string, result: string)
{
    multiset(s) == multiset(result)
}

// <vc-helpers>
lemma MultisetPreservedByAppend<T>(a: seq<T>, b: seq<T>)
    ensures multiset(a + b) == multiset(a) + multiset(b)
{}

lemma MultisetPreservedByUpdate<T>(a: seq<T>, i: int, v: T)
    requires 0 <= i < |a|
    ensures multiset(a[i := v]) == multiset(a) - multiset([a[i]]) + multiset([v])
{
    assert a == a[..i] + [a[i]] + a[i+1..];
    assert a[i := v] == a[..i] + [v] + a[i+1..];
    MultisetPreservedByAppend(a[..i], [a[i]] + a[i+1..]);
    MultisetPreservedByAppend(a[..i], [v] + a[i+1..]);
}

lemma MultisetPreservedBySwap<T>(a: seq<T>, i: int, j: int)
    requires 0 <= i < |a| && 0 <= j < |a|
    ensures multiset(a[i := a[j]][j := a[i]]) == multiset(a)
{
    MultisetPreservedByUpdate(a, i, a[j]);
    MultisetPreservedByUpdate(a[i := a[j]], j, a[i]);
    calc {
        multiset(a[i := a[j]][j := a[i]]);
        multiset((a[i := a[j]])[j := a[i]]);
        multiset(a[i := a[j]]) - multiset([(a[i := a[j]])[j]]) + multiset([a[i]]);
        (multiset(a) - multiset([a[i]]) + multiset([a[j]])) - multiset([a[j]]) + multiset([a[i]]);
        multiset(a);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures ValidOutput(result, n)
    ensures PreservesCharacters(s, result)
// </vc-spec>
// <vc-code>
{
    result := s;
    var m: nat := n / 2;
    for i := 0 to m
        invariant 0 <= i <= m
        invariant |result| == n
        invariant ValidOutput(result, n)
        invariant multiset(result) == multiset(s)
    {
        var j := n - 1 - i;
        if i != j {
            result := result[i := result[j]][j := result[i]];
            MultisetPreservedBySwap(result, i, j);
        }
    }
}
// </vc-code>

