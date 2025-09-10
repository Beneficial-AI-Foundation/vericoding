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
function split(s: string, delimiter: char): seq<string>

lemma InterleaveEqualCorrectness(O: string, E: string, i: nat, result: string)
    requires |O| == |E|
    requires i <= |O|
    requires |result| == 2 * i
    requires forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
    ensures result + InterleaveEqual(O[i..], E[i..]) == InterleaveEqual(O, E)
{
    if i == |O| {
        assert O[i..] == "";
        assert E[i..] == "";
    } else {
        var next_result := result + [O[i], E[i]];
        InterleaveEqualCorrectness(O, E, i + 1, next_result);
    }
}

lemma InterleaveUnequalCorrectness(O: string, E: string, i: nat, result: string)
    requires |O| == |E| + 1
    requires i <= |E|
    requires |result| == 2 * i
    requires forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
    ensures result + InterleaveUnequal(O[i..], E[i..]) == InterleaveUnequal(O, E)
{
    if i == |E| {
        assert E[i..] == "";
        assert O[i..] == [O[i]];
    } else {
        var next_result := result + [O[i], E[i]];
        InterleaveUnequalCorrectness(O, E, i + 1, next_result);
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
    var lines := split(input, '\n');
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    
    result := "";
    
    if a == b {
        var i := 0;
        while i < a
            invariant 0 <= i <= a
            invariant |result| == 2 * i
            invariant forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
        {
            result := result + [O[i], E[i]];
            i := i + 1;
        }
        InterleaveEqualCorrectness(O, E, a, result);
    } else {
        var i := 0;
        while i < b
            invariant 0 <= i <= b
            invariant |result| == 2 * i
            invariant forall k :: 0 <= k < i ==> result[2*k] == O[k] && result[2*k+1] == E[k]
        {
            result := result + [O[i], E[i]];
            i := i + 1;
        }
        result := result + [O[b]];
        InterleaveUnequalCorrectness(O, E, b, result[..|result|-1]);
    }
}
// </vc-code>

