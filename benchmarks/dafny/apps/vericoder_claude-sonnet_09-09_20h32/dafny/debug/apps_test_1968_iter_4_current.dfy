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
    ensures Min(s) in s
    ensures forall x :: x in s ==> Min(s) <= x
{
    if |s| == 1 then s[0]
    else if s[0] <= Min(s[1..]) then s[0]
    else Min(s[1..])
}

lemma MinProperties(s: seq<int>)
    requires |s| > 0
    ensures Min(s) in s
    ensures forall x :: x in s ==> Min(s) <= x
{
    if |s| == 1 {
        // Base case
    } else {
        MinProperties(s[1..]);
        if s[0] <= Min(s[1..]) {
            // Min(s) == s[0], need to prove s[0] <= x for all x in s
            assert forall x :: x in s[1..] ==> Min(s[1..]) <= x;
            assert forall x :: x in s[1..] ==> s[0] <= Min(s[1..]) <= x;
        } else {
            // Min(s) == Min(s[1..]), need to prove Min(s[1..]) <= s[0]
            assert Min(s[1..]) < s[0];
        }
    }
}

lemma InSequenceProperty(x: int, indices: seq<int>)
    requires forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1]
    ensures (x in indices) <==> (exists i :: 0 <= i < |indices| && indices[i] == x)
{
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
    count := 0;
    indices := [];
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant count == |indices|
        invariant count <= i
        invariant forall j :: 0 <= j < |indices| ==> 1 <= indices[j] <= n
        invariant forall j :: 0 <= j < |indices| - 1 ==> indices[j] < indices[j+1]
        invariant forall j :: 0 <= j < |indices| ==> v > Min(sellers[indices[j] - 1])
        invariant forall j :: 0 <= j < i ==> (v > Min(sellers[j]) <==> (j + 1) in indices)
        invariant forall j :: 0 <= j < |indices| ==> indices[j] <= i
    {
        MinProperties(sellers[i]);
        
        if v > Min(sellers[i]) {
            indices := indices + [i + 1];
            count := count + 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>

