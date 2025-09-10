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

function countCharIterative(s: string, c: char): nat
{
    if |s| == 0 then 0
    else if s[0] == c then 1 + countCharIterative(s[1..], c)
    else countCharIterative(s[1..], c)
}

lemma CountCharEquivalence(s: string, c: char)
    ensures countChar(s, c) == countCharIterative(s, c)
{
    var setCount := |set i | 0 <= i < |s| && s[i] == c|;
    if |s| == 0 {
        assert setCount == 0;
        assert countCharIterative(s, c) == 0;
    } else {
        var restSet := set i | 0 <= i < |s[1..]| && s[1..][i] == c;
        var fullSet := set i | 0 <= i < |s| && s[i] == c;
        
        if s[0] == c {
            assert fullSet == {0} + (set i | i in restSet :: i + 1);
            assert |fullSet| == 1 + |restSet|;
        } else {
            assert fullSet == (set i | i in restSet :: i + 1);
            assert |fullSet| == |restSet|;
        }
        
        CountCharEquivalence(s[1..], c);
    }
}

function repeatChar(c: char, n: nat): string
{
    if n == 0 then ""
    else [c] + repeatChar(c, n - 1)
}

lemma RepeatCharLength(c: char, n: nat)
    ensures |repeatChar(c, n)| == n
{
    if n == 0 {
    } else {
        RepeatCharLength(c, n - 1);
    }
}

lemma RepeatCharContent(c: char, n: nat)
    ensures forall i :: 0 <= i < |repeatChar(c, n)| ==> repeatChar(c, n)[i] == c
{
    if n == 0 {
    } else {
        RepeatCharContent(c, n - 1);
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
    CountCharEquivalence(s, 'x');
    CountCharEquivalence(s, 'y');
    
    var countX := countCharIterative(s, 'x');
    var countY := countCharIterative(s, 'y');
    
    if countY > countX {
        result := repeatChar('y', countY - countX);
        RepeatCharLength('y', countY - countX);
        RepeatCharContent('y', countY - countX);
    } else {
        result := repeatChar('x', countX - countY);
        RepeatCharLength('x', countX - countY);
        RepeatCharContent('x', countX - countY);
    }
}
// </vc-code>

