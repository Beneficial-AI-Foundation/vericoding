// <vc-preamble>
// ======= TASK =======
// Given a list of integers, return a new list where each element is incremented by 1.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method incr_list(l: seq<int>) returns (result: seq<int>)
    requires ValidInput(l)
    ensures CorrectOutput(l, result)
// </vc-spec>
// <vc-code>
{
    var tmpCall1 := seq(|l|, i requires 0 <= i < |l| => l[i] + 1);
    result := tmpCall1;
}
// </vc-code>
