predicate ValidInput(testCases: seq<(int, int, seq<(int, int)>)>)
{
    |testCases| >= 0 &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        n >= 1 && 1 <= x <= n && |operations| >= 0 &&
        (forall j :: 0 <= j < |operations| ==> 
            var (l, r) := operations[j];
            1 <= l <= r <= n)
}

function computeFinalBounds(x: int, operations: seq<(int, int)>): (int, int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
{
    computeFinalBoundsHelper(x, x, operations, 0)
}

predicate ValidResults(testCases: seq<(int, int, seq<(int, int)>)>, results: seq<int>)
    requires ValidInput(testCases)
{
    |results| == |testCases| &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        var finalBounds := computeFinalBounds(x, operations);
        results[i] == finalBounds.1 - finalBounds.0 + 1 &&
        finalBounds.0 <= x <= finalBounds.1 &&
        results[i] >= 1 &&
        1 <= finalBounds.0 <= finalBounds.1 <= n
}

// <vc-helpers>
function computeFinalBoundsHelper(lo: int, hi: int, ops: seq<(int, int)>, i: int): (int, int)
    requires 0 <= i <= |ops|
    requires lo <= hi
    requires forall j :: 0 <= j < |ops| ==> ops[j].0 <= ops[j].1
    decreases |ops| - i
    ensures result.0 <= result.1
    ensures result.0 <= lo && hi <= result.1
    ensures forall a:int, b:int ::
        (a <= lo && hi <= b &&
         (forall j :: i <= j < |ops| ==> a <= ops[j].0 && ops[j].1 <= b)) ==> a <= result.0 && result.1 <= b
{
    if i == |ops| then (lo, hi)
    else if ops[i].1 < lo || hi < ops[i].0 then
        computeFinalBoundsHelper(lo, hi, ops, i + 1)
    else
        computeFinalBoundsHelper(
            if ops[i].0 < lo then ops[i].0 else lo,
            if hi < ops[i].1 then ops[i].1 else hi,
            ops, i + 1)
}

function finalLength(x: int, operations: seq<(int, int)>): int
    requires forall j :: 0 <= j < |operations| ==> operations[j].0 <= operations[j].1
{
    computeFinalBounds(x, operations).1 - computeFinalBounds(x, operations).0 + 1
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
  results := seq i | 0 <= i < |testCases| ::
    finalLength(testCases[i].1, testCases[i].2);
}
// </vc-code>

