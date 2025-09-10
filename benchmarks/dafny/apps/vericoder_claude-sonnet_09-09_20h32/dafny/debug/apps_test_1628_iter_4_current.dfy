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
}

lemma CountCharIterativeCorrect(s: string, c: char)
    requires forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
    ensures countCharIterative(s, c) == countChar(s, c)
{
    if |s| == 0 {
    } else {
        SetShiftLemma(s, c);
        CountCharIterativeCorrect(s[1..], c);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    var countX := countCharIterative(s, 'x');
    var countY := countCharIterative(s, 'y');
    
    CountCharIterativeCorrect(s, 'x');
    CountCharIterativeCorrect(s, 'y');
    
    if countY > countX {
        result := "";
        var i := 0;
        while i < countY - countX
            invariant 0 <= i <= countY - countX
            invariant |result| == i
            invariant forall j :: 0 <= j < i ==> result[j] == 'y'
        {
            result := result + "y";
            i := i + 1;
        }
    } else {
        result := "";
        var i := 0;
        while i < countX - countY
            invariant 0 <= i <= countX - countY
            invariant |result| == i
            invariant forall j :: 0 <= j < i ==> result[j] == 'x'
        {
            result := result + "x";
            i := i + 1;
        }
    }
}
// </vc-code>

