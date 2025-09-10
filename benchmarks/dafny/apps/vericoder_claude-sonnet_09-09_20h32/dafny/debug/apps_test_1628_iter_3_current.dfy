predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
}

function countChar(s: string, c: char): nat
{
    |set i | 0 <= i < |s| && s[i] == c|
}

predicate ValidOutput(s: string, result: string)
    requires ValidInput(s)
{
    var countX := countChar(s, 'x');
    var countY := countChar(s, 'y');
    if countY > countX then
        |result| == countY - countX && forall i :: 0 <= i < |result| ==> result[i] == 'y'
    else
        |result| == countX - countY && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
lemma CountCharCorrect(s: string, c: char, count: nat)
    requires forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
    ensures count == countChar(s, c) <==> count == |set i | 0 <= i < |s| && s[i] == c|
{
}

function countCharIterative(s: string, c: char): nat
{
    if |s| == 0 then 0
    else if s[0] == c then 1 + countCharIterative(s[1..], c)
    else countCharIterative(s[1..], c)
}

lemma SetShiftLemma(s: string, c: char)
    requires |s| > 0
    ensures (set i | 0 <= i < |s[1..]| && s[1..][i] == c) == (set i | 1 <= i < |s| && s[i] == c)
{
    var restSet := set i | 0 <= i < |s[1..]| && s[1..][i] == c;
    var shiftedSet := set i | 1 <= i < |s| && s[i] == c;
    
    // Show restSet is subset of shifte
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
lemma CountCharCorrect(s: string, c: char, count: nat)
    requires forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
    ensures count == countChar(s, c) <==> count == |set i | 0 <= i < |s| && s[i] == c|
{
}

function countCharIterative(s: string, c: char): nat
{
    if |s| == 0 then 0
    else if s[0] == c then 1 + countCharIterative(s[1..], c)
    else countCharIterative(s[1..], c)
}

lemma SetShiftLemma(s: string, c: char)
    requires |s| > 0
    ensures (set i | 0 <= i < |s[1..]| && s[1..][i] == c) == (set i | 1 <= i < |s| && s[i] == c)
{
    var restSet := set i | 0 <= i < |s[1..]| && s[1..][i] == c;
    var shiftedSet := set i | 1 <= i < |s| && s[i] == c;
    
    // Show restSet is subset of shifte
// </vc-code>

