// <vc-preamble>

predicate ValidInput(l: seq<int>)
{
    true
}

predicate CorrectOutput(l: seq<int>, result: seq<int>)
{
    |result| == |l| && 
    forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
}
// </vc-preamble>

// <vc-helpers>
function incr(x: int): int { x + 1 }

function incr_seq(s: seq<int>): seq<int>
    ensures |incr_seq(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> incr_seq(s)[i] == s[i] + 1
{
    if |s| == 0 then []
    else [incr(s[0])] + incr_seq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    requires ValidInput(l)
    ensures CorrectOutput(l, result)
// </vc-spec>
// <vc-code>
{
    result := incr_seq(l);
}
// </vc-code>
