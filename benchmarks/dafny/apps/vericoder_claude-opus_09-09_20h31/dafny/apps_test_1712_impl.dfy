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
    requires k >= 0
{
    if k == 0 then 2  // Both lose
    else if k <= a then 0  // Vanya wins
    else 1  // Vova wins
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, mobs: seq<int>) returns (result: seq<string>)
    requires ValidInput(n, a, b, mobs)
    ensures CorrectResult(result, n, a, b, mobs)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            var total := a + b;
            var k := if mobs[j] == 0 then 0 else mobs[j] % total;
            (result[j] == "Vanya" <==> determineWinner(k, a, b) == 0) &&
            (result[j] == "Vova" <==> determineWinner(k, a, b) == 1) &&
            (result[j] == "Both" <==> determineWinner(k, a, b) == 2)
        invariant forall j :: 0 <= j < i ==> result[j] in ["Vanya", "Vova", "Both"]
    {
        var total := a + b;
        var k := if mobs[i] == 0 then 0 else mobs[i] % total;
        var winner := determineWinner(k, a, b);
        
        if winner == 0 {
            result := result + ["Vanya"];
        } else if winner == 1 {
            result := result + ["Vova"];
        } else {
            result := result + ["Both"];
        }
        
        i := i + 1;
    }
}
// </vc-code>

