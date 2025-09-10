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
    if total == 0 then 2 // Should not happen given a,b > 0, but as a safeguard
    else if 0 <= k < a then 0 // Vanya wins
    else if a <= k < total then 1 // Vova wins
    else 2 // k >= total, meaning k wraps around effectively behaving like 0. It means both are possible (due to remainder being 0)
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
        invariant ValidOutput(newResult[..i], i)
        invariant forall j :: 0 <= j < i ==>
            var total := a + b;
            var k_j := if mobs[j] == 0 then 0 else mobs[j] % total;
            (newResult[j] == "Vanya" <==> determineWinner(k_j, a, b) == 0) &&
            (newResult[j] == "Vova" <==> determineWinner(k_j, a, b) == 1) &&
            (newResult[j] == "Both" <==> determineWinner(k_j, a, b) == 2)
    {
        var total := a + b;
        var k := if mobs[i] == 0 then 0 else mobs[i] % total;

        var winner: string;
        if (mobs[i] == 0) { // Special case from problem, 0 mob means Both
          winner := "Both";
        } else {
            var dw_result := determineWinner(k, a, b);
            if dw_result == 0 then winner := "Vanya"
            else if dw_result == 1 then winner := "Vova"
            else winner := "Both";
        }

        newResult := newResult[i := winner];
        i := i + 1;
    }
    return newResult;
}
// </vc-code>

