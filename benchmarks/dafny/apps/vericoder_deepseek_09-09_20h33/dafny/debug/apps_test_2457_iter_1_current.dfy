predicate ValidInput(input: string) {
    |input| >= 0
}

predicate ValidTestCase(n: int, a: int, b: int, c: int, d: int) {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

function CanAchieveWeight(n: int, a: int, b: int, c: int, d: int): bool {
    var minWeight := (a - b) * n;
    var maxWeight := (a + b) * n;
    var targetMin := c - d;
    var targetMax := c + d;
    !(minWeight > targetMax || maxWeight < targetMin)
}

predicate ValidOutput(output: string) {
    forall i :: 0 <= i < |output| ==> output[i] in "YesNo\n"
}

// <vc-helpers>
lemma Lemma_MultiplicationBounds(n: int, a: int, b: int)
    requires n >= 1 && a >= 0 && b >= 0 && b < a
    ensures (a - b) * n >= 0
    ensures (a + b) * n >= 0
{
}

lemma Lemma_WeightInRange(n: int, a: int, b: int, weight: int)
    requires n >= 1 && a >= 0 && b >= 0 && b < a
    requires weight >= (a - b) * n && weight <= (a + b) * n
    ensures !((a - b) * n > (weight) || (a + b) * n < (weight))
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures (input == "" || input == "\n") ==> result == ""
    ensures input != "" && input != "\n" ==> (|result| > 0 ==> result[|result|-1] == '\n' || (|result| > 3 && result[|result|-4..] in ["Yes\n", "No\n"]))
// </vc-spec>
// <vc-code>
{
    result := "";
    if input == "" || input == "\n" {
        return;
    }
    
    var lines := input.Split('\n');
    var t := lines[0].AsInt();
    var index := 1;
    
    while index <= t
        invariant index >= 1 && index <= t + 1
        invariant |result| >= 0
    {
        var parts := lines[index].Split(' ');
        var n := parts[0].AsInt();
        var a := parts[1].AsInt();
        var b := parts[2].AsInt();
        var c := parts[3].AsInt();
        var d := parts[4].AsInt();
        
        assert ValidTestCase(n, a, b, c, d);
        Lemma_MultiplicationBounds(n, a, b);
        
        if CanAchieveWeight(n, a, b, c, d) {
            result := result + "Yes\n";
        } else {
            result := result + "No\n";
        }
        
        index := index + 1;
    }
}
// </vc-code>

