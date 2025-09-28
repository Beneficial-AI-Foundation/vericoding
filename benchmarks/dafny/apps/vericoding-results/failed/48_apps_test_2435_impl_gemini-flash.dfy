// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add requires clause for helper function. */
function computeFinalBoundsHelper(currentL: int, currentR: int, operations: seq<(int, int)>, idx: int): (int, int)
    requires 0 <= idx <= |operations|
    requires currentL <= currentR
    decreases |operations| - idx
    ensures var (finalL, finalR) := computeFinalBoundsHelper(currentL, currentR, operations, idx);
            finalL <= finalR + 1 // finalL can be R+1 if intersection is empty, e.g. (1,0)
{
    if idx == |operations| then
        (currentL, currentR)
    else
        var (l, r) := operations[idx];
        var newL := if l > currentL then l else currentL;
        var newR := if r < currentR then r else currentR;
        if newL > newR then
            (1, 0) // Indicate an empty intersection
        else
            computeFinalBoundsHelper(newL, newR, operations, idx + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed return res.seq; to results := res; and fixed the invariant to match the ValidResults property. */
{
  var res: array<int> := new int[|testCases|];
  for i := 0 to |testCases| - 1
    invariant 0 <= i <= |testCases|
    invariant |res| == |testCases|
    invariant forall k :: 0 <= k < i ==> 
        var (n_k, x_k, ops_k) := testCases[k];
        var finalBounds_k := computeFinalBounds(x_k, ops_k);
        res[k] == finalBounds_k.1 - finalBounds_k.0 + 1 &&
        finalBounds_k.0 <= x_k <= finalBounds_k.1 &&
        res[k] >= 1 &&
        1 <= finalBounds_k.0 <= finalBounds_k.1 <= n_k
{
    var (n, x, operations) := testCases[i];

    var currentL := x;
    var currentR := x;

    var finalBounds := computeFinalBoundsHelper(currentL, currentR, operations, 0);
    var finalL := finalBounds.0;
    var finalR := finalBounds.1;

    if finalL > finalR {
        res[i] := 0; // Indicate an empty intersection resulted in 0 valid positions
    } else {
        res[i] := finalR - finalL + 1;
    }
  }
  results := res;
}
// </vc-code>
