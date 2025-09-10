predicate ValidInput(testCases: seq<(int, int)>)
{
    forall i :: 0 <= i < |testCases| ==> 
        0 <= testCases[i].0 < 24 && 
        0 <= testCases[i].1 < 60 && 
        !(testCases[i].0 == 0 && testCases[i].1 == 0)
}

function MinutesUntilMidnight(h: int, m: int): int
    requires 0 <= h < 24
    requires 0 <= m < 60
    requires !(h == 0 && m == 0)
{
    1440 - (h * 60 + m)
}

predicate ValidOutput(results: seq<int>)
{
    forall i :: 0 <= i < |results| ==> 1 <= results[i] <= 1439
}

// <vc-helpers>
function SeqFromArray<T>(arr: array<T>): seq<T>
  reads arr
  ensures |SeqFromArray(arr)| == arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> SeqFromArray(arr)[i] == arr[i]
{
  if arr.Length == 0 then [] else arr[0] + SeqFromArray(arr[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures |results| == |testCases|
    ensures forall i :: 0 <= i < |results| ==> results[i] == MinutesUntilMidnight(testCases[i].0, testCases[i].1)
    ensures ValidOutput(results)
// </vc-spec>
// <vc-code>
{
    var results_arr := new int[|testCases|];
    for i := 0 to |testCases| - 1
        invariant 0 <= i <= |testCases|
        invariant forall k :: 0 <= k < i ==> results_arr[k] == MinutesUntilMidnight(testCases[k].0, testCases[k].1)
        invariant forall k :: 0 <= k < i ==> 1 <= results_arr[k] <= 1439
    {
        results_arr[i] := MinutesUntilMidnight(testCases[i].0, testCases[i].1);
    }
    results := SeqFromArray(results_arr);
}
// </vc-code>

