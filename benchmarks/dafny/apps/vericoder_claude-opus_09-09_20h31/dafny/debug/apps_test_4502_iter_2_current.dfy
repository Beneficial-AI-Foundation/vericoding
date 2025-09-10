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
lemma reverseSeqIndex(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures reverseSeq(s)[i] == s[|s| - 1 - i]
{
    // This follows directly from the postcondition of reverseSeq
}

lemma reverseSeqConcat(s1: seq<int>, s2: seq<int>)
    ensures reverseSeq(s1 + s2) == reverseSeq(s2) + reverseSeq(s1)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        reverseSeqConcat(s1[1..], s2);
    }
}

lemma ArrayToSeqEquality<T>(a: array<T>, s: seq<T>)
    requires s == a[..]
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{
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
    var o_len := if n % 2 == 0 then n / 2 else (n + 1) / 2;
    var e_len := n / 2;
    
    var o := new int[o_len];
    var e := new int[e_len];
    
    var i := 0;
    while i < o_len
        invariant 0 <= i <= o_len
        invariant forall j :: 0 <= j < i ==> o[j] == a[2*j]
    {
        o[i] := a[2*i];
        i := i + 1;
    }
    
    i := 0;
    while i < e_len
        invariant 0 <= i <= e_len
        invariant forall j :: 0 <= j < i ==> e[j] == a[2*j + 1]
    {
        e[i] := a[2*i + 1];
        i := i + 1;
    }
    
    var o_seq := o[..];
    var e_seq := e[..];
    
    ArrayToSeqEquality(o, o_seq);
    ArrayToSeqEquality(e, e_seq);
    
    assert |o_seq| == o_len;
    assert |e_seq| == e_len;
    assert forall j :: 0 <= j < o_len ==> o_seq[j] == a[2*j];
    assert forall j :: 0 <= j < e_len ==> e_seq[j] == a[2*j + 1];
    
    var reversed_o := new int[o_len];
    var reversed_e := new int[e_len];
    
    i := 0;
    while i < o_len
        invariant 0 <= i <= o_len
        invariant forall j :: 0 <= j < i ==> reversed_o[j] == o_seq[o_len - 1 - j]
    {
        reversed_o[i] := o_seq[o_len - 1 - i];
        i := i + 1;
    }
    
    i := 0;
    while i < e_len
        invariant 0 <= i <= e_len
        invariant forall j :: 0 <= j < i ==> reversed_e[j] == e_seq[e_len - 1 - j]
    {
        reversed_e[i] := e_seq[e_len - 1 - i];
        i := i + 1;
    }
    
    var reversed_o_seq := reversed_o[..];
    var reversed_e_seq := reversed_e[..];
    
    ArrayToSeqEquality(reversed_o, reversed_o_seq);
    ArrayToSeqEquality(reversed_e, reversed_e_seq);
    
    assert |reversed_o_seq| == o_len;
    assert |reversed_e_seq| == e_len;
    assert forall j :: 0 <= j < o_len ==> reversed_o_seq[j] == o_seq[o_len - 1 - j];
    assert forall j :: 0 <= j < e_len ==> reversed_e_seq[j] == e_seq[e_len - 1 - j];
    
    assert reversed_o_seq == reverseSeq(o_seq);
    assert reversed_e_seq == reverseSeq(e_seq);
    
    if n % 2 == 0 {
        result := reversed_e_seq + o_seq;
    } else {
        result := reversed_o_seq + e_seq;
    }
    
    assert result == computeResult(a);
}
// </vc-code>

