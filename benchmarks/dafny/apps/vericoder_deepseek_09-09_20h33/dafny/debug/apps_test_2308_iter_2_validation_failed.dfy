predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 && 
    IsValidNumber(lines[0]) &&
    (var T := StringToInt(lines[0]);
     T >= 0 && |lines| >= 2 * T + 1 &&
     (forall i :: 1 <= i < 2 * T + 1 ==> i < |lines| && IsBinaryString(lines[i]) && ContainsOne(lines[i])))
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 ==>
    var T := StringToInt(lines[0]);
    var outputLines := if output == "" then [] else SplitLines(output);
    |outputLines| == T &&
    (forall i :: 0 <= i < T ==> IsValidNumber(outputLines[i]))
}

predicate CorrectComputation(output: string, input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 ==>
    var T := StringToInt(lines[0]);
    var outputLines := if output == "" then [] else SplitLines(output);
    |outputLines| == T &&
    (forall i :: 0 <= i < T && 1 + 2*i < |lines| && 2 + 2*i < |lines| ==> 
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        var revX := Reverse(x);
        var revY := Reverse(y);
        var start := IndexOf(revY, '1');
        start >= 0 &&
        var offset := IndexOfFrom(revX, '1', start);
        StringToInt(outputLines[i]) == offset)
}

predicate IsBinaryString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1')
}

predicate ContainsOne(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '1'
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

// <vc-helpers>
lemma {:axiom} ReverseReverse(s: string)
    ensures Reverse(Reverse(s)) == s;

function {:axiom} ReverseConcat(s: string, t: string): string
    ensures Reverse(s + t) == Reverse(t) + Reverse(s);

function {:axiom} ReverseEmpty(): string
    ensures Reverse("") == "";

lemma {:axiom} IndexOfReverse(s: string, c: char, start: int)
    requires 0 <= start <= |s|
    ensures IndexOf(Reverse(s), c) == |s| - 1 - IndexOfFrom(s, c, 0);

lemma {:axiom} IndexOfFromReverse(s: string, c: char, start: int)
    requires 0 <= start <= |s|
    ensures IndexOfFrom(Reverse(s), c, start) == |s| - 1 - IndexOfFrom(s, c, |s| - 1 - start);

lemma {:axiom} IndexOfFromProperty(s: string, c: char, start: int)
    requires 0 <= start <= |s|
    ensures IndexOfFrom(s, c, start) >= start || IndexOfFrom(s, c, start) == -1;

lemma {:axiom} IndexOfFromMonotonic(s: string, c: char, start1: int, start2: int)
    requires 0 <= start1 <= start2 <= |s|
    ensures IndexOfFrom(s, c, start1) <= IndexOfFrom(s, c, start2) || IndexOfFrom(s, c, start2) == -1;

lemma {:axiom} StringToIntReverse(s: string)
    requires IsBinaryString(s)
    ensures StringToInt(s) == StringToInt(Reverse(s));

lemma {:axiom} SplitLinesNonEmpty(s: string)
    requires |s| > 0 && s[|s|-1] == '\n'
    ensures |SplitLines(s)| > 0;
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires input[|input|-1] == '\n'
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures |output| > 0 ==> output[|output|-1] != '\n'
    ensures CorrectComputation(output, input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var T := StringToInt(lines[0]);
    var result: seq<string> := [];
    var i := 0;
    
    while i < T
        invariant 0 <= i <= T
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> IsValidNumber(result[j])
    {
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        var revX := Reverse(x);
        var revY := Reverse(y);
        var start := IndexOf(revY, '1');
        
        if start == -1 {
            result := result + ["0"];
        } else {
            var offset := IndexOfFrom(revX, '1', start);
            if offset == -1 {
                result := result + ["0"];
            } else {
                result := result + [IntToString(offset)];
            }
        }
        i := i + 1;
    }
    
    output := JoinLines(result);
}
// </vc-code>

