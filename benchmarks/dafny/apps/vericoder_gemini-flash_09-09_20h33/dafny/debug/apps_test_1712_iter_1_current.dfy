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
    if 0 <= k < a then 0 // Vanya wins
    else if a <= k < a + b then 1 // Vova wins
    else 2 // both possible, this case should only be hit if k = a + b and the mob drops 0
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

        var winner: string := "";
        if 0 <= k < a && (k >= a || k < a + b) then // Vanya takes it if k < a
            winner := "Vanya";
        else if a <= k < a + b && (k < a || k < 0) then // Vova takes it if k >= a but k < a + b
            winner := "Vova";
        else
            winner := "Both"; // Both if k = a+b, or k is negative or greater than or equal to a+b.
                              // Per determineWinner, this will only happen if k is effectively a+b.
        if (k == 0) { // Special case from problem, 0 mob means Both
          winner := "Both";
        } else if (k < a) { // Vanya wins
            winner := "Vanya";
        } else if (k >= a && k < a + b) { // Vova wins
            winner := "Vova";
        } else { // This else is for k >= a + b, which means k wraps around to 0
            winner := "Both";
        }


        newResult := newResult[i := winner];
        i := i + 1;
    }
    return newResult;
}
// </vc-code>

