predicate ValidInput(n: int, a: int, b: int, mobs: seq<int>)
{
    n >= 0 && a > 0 && b > 0 && |mobs| == n &&
    forall i :: 0 <= i < n ==> mobs[i] >= 0
}

predicate ValidOutput(result: seq<string>, n: int)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] in ["Vanya", "Vova", "Both"]
}

predicate CorrectResult(result: seq<string>, n: int, a: int, b: int, mobs: seq<int>)
    requires a > 0 && b > 0 && |mobs| == n
{
    ValidOutput(result, n) &&
    forall i :: 0 <= i < n ==> 
        var total := a + b;
        var k := if mobs[i] == 0 then 0 else mobs[i] % total;
        (result[i] == "Vanya" <==> determineWinner(k, a, b) == 0) &&
        (result[i] == "Vova" <==> determineWinner(k, a, b) == 1) &&
        (result[i] == "Both" <==> determineWinner(k, a, b) == 2)
}

// <vc-helpers>
function determineWinner(k: int, a: int, b: int): int
    requires a > 0 && b > 0
    ensures determineWinner(k, a, b) in [0, 1, 2] // 0 for Vanya, 1 for Vova, 2 for Both
{
    var total := a + b;
    // k effectively represents mobs[i] % total.
    // If the original mobs[i] was 0, k will also be 0, and handling this via the general logic
    // might lead to "Vanya" winning if 0 < a. 
    // However, the problem statement implies a direct "Both" for 0 mobs.
    // Therefore, the special case for moods[i] == 0 is handled in the solve method itself.
    // The determineWinner function should correctly classify k for k > 0.
    
    // The ensures clause simplifies to a check on the return value's range.

    // k is the remainder of mobs[i] / (a + b). It will always be non-negative.
    // By definition of remainder, 0 <= k < total (if total > 0).

    if total == 0 then 2 // This case should not be reached given a, b > 0
    else if 0 <= k < a then 0 // Vanya wins: k is in [0, a-1]
    else if a <= k < total then 1 // Vova wins: k is in [a, total-1]
    else 2 // This case (k >= total) should not occur given the definition of k = mobs[i] % total
           // but adding it for completeness to satisfy the ensures clause for all k.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, mobs: seq<int>) returns (result: seq<string>)
    requires ValidInput(n, a, b, mobs)
    ensures CorrectResult(result, n, a, b, mobs)
// </vc-spec>
// <vc-code>
{
    var newResult: seq<string> := new seq<string>(n, i => "");
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |newResult| == n
        invariant forall j :: 0 <= j < i ==>
            var total := a + b;
            var k_j := if mobs[j] == 0 then 0 else mobs[j] % total;
            // The logic for 'Both' from mobs[j] == 0 needs to be reflected here for correctness.
            (mobs[j] == 0 && newResult[j] == "Both") ||
            (mobs[j] != 0 && (
                (newResult[j] == "Vanya" <==> determineWinner(k_j, a, b) == 0) &&
                (newResult[j] == "Vova" <==> determineWinner(k_j, a, b) == 1) &&
                (newResult[j] == "Both" <==> determineWinner(k_j, a, b) == 2)
            ))
        invariant forall j :: 0 <= j < i ==> newResult[j] in ["Vanya", "Vova", "Both"]
    {
        var total := a + b;
        var k := if mobs[i] == 0 then 0 else mobs[i] % total;

        var winner: string;
        if (mobs[i] == 0) { // Special case from problem, 0 mob means Both
          winner := "Both";
        } else {
            var dw_result := determineWinner(k, a, b);
            if dw_result == 0 { winner := "Vanya"; }
            else if dw_result == 1 { winner := "Vova"; }
            else { winner := "Both"; }
        }

        newResult := newResult[i := winner];
        i := i + 1;
    }
    return newResult;
}
// </vc-code>

