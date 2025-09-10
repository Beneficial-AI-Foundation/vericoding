predicate ValidInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 &&
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    (a == b || a == b + 1) &&
    (a > 0 || b == 0)
}

function GetO(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[0]
}

function GetE(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[1]
}

function CorrectResult(input: string): string
    requires ValidInput(input)
{
    var O := GetO(input);
    var E := GetE(input);
    var a := |O|;
    var b := |E|;
    if a == b then
        InterleaveEqual(O, E)
    else
        InterleaveUnequal(O, E)
}

function InterleaveEqual(O: string, E: string): string
    requires |O| == |E|
{
    if |O| == 0 then ""
    else [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
}

function InterleaveUnequal(O: string, E: string): string
    requires |O| == |E| + 1
{
    if |E| == 0 then O
    else [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..])
}

// <vc-helpers>
lemma InterleaveEqualLemma(O: string, E: string, n: nat)
    requires |O| == |E|
    requires n <= |O|
    ensures InterleaveEqual(O, E)[..2*n] == InterleaveEqual(O[..n], E[..n])
    decreases |O| - n
{
    if n == 0 {
    } else {
        InterleaveEqualLemma(O[1..], E[1..], n-1);
    }
}

lemma InterleaveUnequalLemma(O: string, E: string, n: nat)
    requires |O| == |E| + 1
    requires n <= |E|
    ensures InterleaveUnequal(O, E)[..2*n] == InterleaveEqual(O[..n], E[..n])
    decreases |E| - n
{
    if n == 0 {
    } else {
        InterleaveUnequalLemma(O[1..], E[1..], n-1);
    }
}

lemma InterleaveEqualLength(O: string, E: string)
    requires |O| == |E|
    ensures |InterleaveEqual(O, E)| == 2 * |O|
    decreases |O|
{
    if |O| > 0 {
        InterleaveEqualLength(O[1..], E[1..]);
    }
}

lemma InterleaveUnequalLength(O: string, E: string)
    requires |O| == |E| + 1
    ensures |InterleaveUnequal(O, E)| == 2 * |E| + 1
    decreases |E|
{
    if |E| > 0 {
        InterleaveUnequalLength(O[1..], E[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == CorrectResult(input)
// </vc-spec>
// <vc-code>
{
    var lines := input.Split('\n');
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    
    result := "";
    var i := 0;
    
    while i < b
        invariant i <= b
        invariant |result| == 2 * i
        invariant result == InterleaveEqual(O[..i], E[..i])
    {
        result := result + [O[i], E[i]];
        i := i + 1;
    }
    
    if a > b {
        result := result + [O[i]];
    }
}
// </vc-code>

