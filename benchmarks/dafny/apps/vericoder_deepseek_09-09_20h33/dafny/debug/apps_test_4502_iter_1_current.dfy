predicate ValidInput(n: int, a: seq<int>) {
    n >= 1 && |a| == n
}

function simulateOperations(a: seq<int>): seq<int>
    requires |a| >= 1
    decreases |a|
{
    if |a| == 1 then 
        [a[0]]
    else
        var prev := simulateOperations(a[..|a|-1]);
        reverseSeq(prev + [a[|a|-1]])
}

function computeResult(a: seq<int>): seq<int>
    requires |a| >= 1
    ensures |computeResult(a)| == |a|
{
    var n := |a|;
    var o := seq(if n % 2 == 0 then n / 2 else (n + 1) / 2, i requires 0 <= i < (if n % 2 == 0 then n / 2 else (n + 1) / 2) => a[2*i]);
    var e := seq(n / 2, i requires 0 <= i < n / 2 => a[2*i + 1]);
    if n % 2 == 0 then
        reverseSeq(e) + o
    else
        reverseSeq(o) + e
}

function reverseSeq(s: seq<int>): seq<int>
    ensures |reverseSeq(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverseSeq(s)[i] == s[|s| - 1 - i]
{
    if |s| == 0 then []
    else reverseSeq(s[1..]) + [s[0]]
}

// <vc-helpers>
lemma reverseSeqConcat(s1: seq<int>, s2: seq<int>)
    ensures reverseSeq(s1 + s2) == reverseSeq(s2) + reverseSeq(s1)
    decreases |s1|, |s2|
{
    if |s1| == 0 {
        assert reverseSeq([] + s2) == reverseSeq(s2) == reverseSeq(s2) + [];
    } else if |s2| == 0 {
        assert reverseSeq(s1 + []) == reverseSeq(s1) == [] + reverseSeq(s1);
    } else {
        calc {
            reverseSeq(s1 + s2);
            reverseSeq((s1 + s2[..|s2|-1]) + [s2[|s2|-1]]);
            reverseSeq([s2[|s2|-1]]) + reverseSeq(s1 + s2[..|s2|-1]);
            [s2[|s2|-1]] + reverseSeq(s1 + s2[..|s2|-1]);
            [s2[|s2|-1]] + (reverseSeq(s2[..|s2|-1]) + reverseSeq(s1));
            ([s2[|s2|-1]] + reverseSeq(s2[..|s2|-1])) + reverseSeq(s1);
            reverseSeq(s2) + reverseSeq(s1);
        }
    }
}

lemma reverseSeqIdentity(s: seq<int>)
    ensures reverseSeq(reverseSeq(s)) == s
    decreases |s|
{
    if |s| == 0 {
        assert reverseSeq(reverseSeq([])) == reverseSeq([]) == [];
    } else {
        calc {
            reverseSeq(reverseSeq(s));
            reverseSeq(reverseSeq(s[1..]) + [s[0]]);
            reverseSeq([s[0]]) + reverseSeq(reverseSeq(s[1..]));
            [s[0]] + s[1..];
            s;
        }
    }
}

lemma simulateOperationsProperty(a: seq<int>, k: int)
    requires |a| >= 1
    requires 0 <= k <= |a|
    ensures simulateOperations(a[..k] + a[k..]) == simulateOperations(a)
{
    // This is a helper lemma that might be needed for more complex proofs
}

lemma computeResultProperty(a: seq<int>)
    ensures computeResult(a) == simulateOperations(a)
{
    // The key lemma connecting computeResult and simulateOperations
    if |a| == 1 {
        assert computeResult(a) == [a[0]] == simulateOperations(a);
    } else {
        var prev := computeResult(a[..|a|-1]);
        calc {
            simulateOperations(a);
            reverseSeq(simulateOperations(a[..|a|-1]) + [a[|a|-1]]);
            reverseSeq(computeResult(a[..|a|-1]) + [a[|a|-1]]);
            computeResult(a);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, a)
    ensures |result| == n
    ensures result == computeResult(a)
// </vc-spec>
// <vc-code>
{
    var result := [];
    if n % 2 == 0 {
        var mid := n / 2;
        var odd := seq(mid, i requires 0 <= i < mid => a[2*i]);
        var even := seq(mid, i requires 0 <= i < mid => a[2*i + 1]);
        result := reverseSeq(even) + odd;
    } else {
        var mid := (n + 1) / 2;
        var odd := seq(mid, i requires 0 <= i < mid => a[2*i]);
        var even := seq(n / 2, i requires 0 <= i < n / 2 => a[2*i + 1]);
        result := reverseSeq(odd) + even;
    }
    return result;
}
// </vc-code>

