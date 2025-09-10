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
    decreases |s1|
{
    if |s1| == 0 {
        assert reverseSeq([] + s2) == reverseSeq(s2);
        assert reverseSeq(s2) + reverseSeq([]) == reverseSeq(s2) + [] == reverseSeq(s2);
    } else {
        reverseSeqConcat(s1[1..], s2);
        calc {
            reverseSeq(s1 + s2);
            reverseSeq([s1[0]] + (s1[1..] + s2));
            reverseSeq(s1[1..] + s2) + [s1[0]];
            (reverseSeq(s2) + reverseSeq(s1[1..])) + [s1[0]];
            reverseSeq(s2) + (reverseSeq(s1[1..]) + [s1[0]]);
            reverseSeq(s2) + reverseSeq(s1);
        }
    }
}

lemma reverseSeqIdentity(s: seq<int>)
    ensures reverseSeq(reverseSeq(s)) == s
    decreases |s|
{
    if |s| == 0 {
    } else {
        reverseSeqIdentity(s[1..]);
        calc {
            reverseSeq(reverseSeq(s));
            reverseSeq(reverseSeq(s[1..]) + [s[0]]);
            reverseSeq([s[0]]) + reverseSeq(reverseSeq(s[1..]));
            [s[0]] + reverseSeq(reverseSeq(s[1..]));
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
    // This lemma is trivially true since a[..k] + a[k..] == a
    // No proof needed beyond the fact that sequence concatenation works this way
}

lemma computeResultProperty(a: seq<int>)
    requires |a| >= 1
    ensures computeResult(a) == simulateOperations(a)
    decreases |a|
{
    if |a| == 1 {
        assert computeResult(a) == [a[0]] == simulateOperations(a);
    } else {
        computeResultProperty(a[..|a|-1]);
        var prev_sim := simulateOperations(a[..|a|-1]);
        var prev_comp := computeResult(a[..|a|-1]);
        assert prev_sim == prev_comp;
        
        if |a| % 2 == 0 {
            var n := |a|;
            var mid := n / 2;
            var o := seq(mid, i requires 0 <= i < mid => a[2*i]);
            var e := seq(mid, i requires 0 <= i < mid => a[2*i + 1]);
            
            // The key insight: a[n-1] is the last element of e
            assert a[|a|-1] == a[2*(mid-1)+1] == e[mid-1];
            
            calc {
                simulateOperations(a);
                reverseSeq(prev_sim + [a[|a|-1]]);
                reverseSeq(prev_comp + [a[|a|-1]]);
                reverseSeq(computeResult(a[..|a|-1]) + [a[|a|-1]]);
                reverseSeq((reverseSeq(e[..|e|-1]) + o) + [e[mid-1]]);
                reverseSeq(reverseSeq(e[..|e|-1]) + (o + [e[mid-1]]));
                reverseSeq(reverseSeq(e[..|e|-1]) + reverseSeq([e[mid-1]] + reverseSeq(o)));
                e[..|e|-1] + reverseSeq([e[mid-1]] + reverseSeq(o));
                reverseSeq([e[mid-1]] + reverseSeq(o)) == reverseSeq(reverseSeq(o)) + [e[mid-1]];
                e[..|e|-1] + (o + [e[mid-1]]);
                reverseSeq(e) + o;
                computeResult(a);
            }
        } else {
            var n := |a|;
            var mid := (n + 1) / 2;
            var o := seq(mid, i requires 0 <= i < mid => a[2*i]);
            var e := seq(n / 2, i requires 0 <= i < n / 2 => a[2*i + 1]);
            
            // The key insight: a[n-1] is the last element of o
            assert a[|a|-1] == a[2*(mid-1)] == o[mid-1];
            
            calc {
                simulateOperations(a);
                reverseSeq(prev_sim + [a[|a|-1]]);
                reverseSeq(prev_comp + [a[|a|-1]]);
                reverseSeq(computeResult(a[..|a|-1]) + [a[|a|-1]]);
                reverseSeq((reverseSeq(o[..|o|-1]) + e) + [o[mid-1]]);
                reverseSeq(reverseSeq(o[..|o|-1]) + (e + [o[mid-1]]));
                reverseSeq(reverseSeq(o[..|o|-1]) + reverseSeq([o[mid-1]] + reverseSeq(e)));
                o[..|o|-1] + reverseSeq([o[mid-1]] + reverseSeq(e));
                reverseSeq([o[mid-1]] + reverseSeq(e)) == reverseSeq(reverseSeq(e)) + [o[mid-1]];
                o[..|o|-1] + (e + [o[mid-1]]);
                reverseSeq(o) + e;
                computeResult(a);
            }
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
    // The implementation correctly matches the computeResult function
    if n % 2 == 0 {
        var mid := n / 2;
        var odd := seq(mid, i requires 0 <= i < mid => a[2*i]);
        var even := seq(mid, i requires 0 <= i < mid => a[2*i + 1]);
        return reverseSeq(even) + odd;
    } else {
        var mid := (n + 1) / 2;
        var odd := seq(mid, i requires 0 <= i < mid => a[2*i]);
        var even := seq(n / 2, i requires 0 <= i < n / 2 => a[2*i + 1]);
        return reverseSeq(odd) + even;
    }
}
// </vc-code>

