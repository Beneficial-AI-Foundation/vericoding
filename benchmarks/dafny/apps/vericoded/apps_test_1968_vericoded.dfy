predicate ValidInput(n: int, v: int, sellers: seq<seq<int>>) {
    n >= 0 && v >= 0 && |sellers| == n && 
    forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
}

predicate ValidOutput(count: int, indices: seq<int>, n: int) {
    count == |indices| && count >= 0 && count <= n &&
    (forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= n) &&
    (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1])
}

predicate CorrectSolution(v: int, sellers: seq<seq<int>>, indices: seq<int>) 
    requires forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
    requires forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= |sellers|
{
    (forall i :: 0 <= i < |indices| ==> v > Min(sellers[indices[i] - 1])) &&
    (forall i :: 0 <= i < |sellers| ==> (v > Min(sellers[i]) <==> (i + 1) in indices))
}

// <vc-helpers>
function Min(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var tailMin := Min(s[1..]);
        if s[0] < tailMin then s[0] else tailMin
}

lemma MinIsInSequence(s: seq<int>)
    requires |s| > 0
    ensures Min(s) in s
{
    if |s| == 1 {
        assert Min(s) == s[0];
        assert s[0] in s;
    } else {
        var tailMin := Min(s[1..]);
        MinIsInSequence(s[1..]);
        assert tailMin in s[1..];
        assert tailMin in s;
        if s[0] < tailMin {
            assert Min(s) == s[0];
            assert s[0] in s;
        } else {
            assert Min(s) == tailMin;
            assert tailMin in s;
        }
    }
}

lemma MinIsMinimal(s: seq<int>, x: int)
    requires |s| > 0
    requires x in s
    ensures Min(s) <= x
{
    if |s| == 1 {
        assert s[0] == x;
        assert Min(s) == s[0];
    } else {
        var tailMin := Min(s[1..]);
        if x == s[0] {
            if s[0] < tailMin {
                assert Min(s) == s[0] == x;
            } else {
                assert Min(s) == tailMin;
                MinIsInSequence(s[1..]);
                assert tailMin in s[1..];
                MinIsMinimal(s[1..], tailMin);
                assert tailMin <= tailMin;
                assert Min(s) <= x;
            }
        } else {
            assert x in s[1..];
            MinIsMinimal(s[1..], x);
            assert tailMin <= x;
            if s[0] < tailMin {
                assert Min(s) == s[0];
                assert s[0] < tailMin <= x;
                assert Min(s) <= x;
            } else {
                assert Min(s) == tailMin;
                assert Min(s) <= x;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int, sellers: seq<seq<int>>) returns (count: int, indices: seq<int>)
    requires ValidInput(n, v, sellers)
    ensures ValidOutput(count, indices, n)
    ensures CorrectSolution(v, sellers, indices)
// </vc-spec>
// <vc-code>
{
    indices := [];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |indices| <= i
        invariant forall j :: 0 <= j < |indices| ==> 1 <= indices[j] <= i
        invariant forall j :: 0 <= j < |indices| - 1 ==> indices[j] < indices[j+1]
        invariant forall j :: 0 <= j < |indices| ==> indices[j] <= n
        invariant forall j :: 0 <= j < |indices| ==> v > Min(sellers[indices[j] - 1])
        invariant forall j :: 0 <= j < i ==> (v > Min(sellers[j]) <==> (j + 1) in indices)
    {
        var minPrice := Min(sellers[i]);
        if v > minPrice {
            indices := indices + [i + 1];
        }
        i := i + 1;
    }
    
    count := |indices|;
}
// </vc-code>

