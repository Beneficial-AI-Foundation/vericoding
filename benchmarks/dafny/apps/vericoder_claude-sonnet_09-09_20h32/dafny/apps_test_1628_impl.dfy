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
    
    // Prove both directions of set equality
    forall x | x in restSet
        ensures x + 1 in shiftedSet
    {
        assert 0 <= x < |s[1..]| && s[1..][x] == c;
        assert s[1..][x] == s[x + 1];
        assert 1 <= x + 1 < |s| && s[x + 1] == c;
    }
    
    forall y | y in shiftedSet
        ensures y - 1 in restSet
    {
        assert 1 <= y < |s| && s[y] == c;
        assert 0 <= y - 1 < |s[1..]| && s[1..][y - 1] == c;
    }
    
    assert restSet == set x | x in restSet :: x + 1;
    assert shiftedSet == set y | y in shiftedSet :: y;
    assert (set x | x in restSet :: x + 1) == shiftedSet;
}

lemma CountCharIterativeCorrect(s: string, c: char)
    requires forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
    ensures countCharIterative(s, c) == countChar(s, c)
{
    if |s| == 0 {
        assert countCharIterative(s, c) == 0;
        assert countChar(s, c) == |set i | 0 <= i < 0 && s[i] == c| == 0;
    } else {
        SetShiftLemma(s, c);
        CountCharIterativeCorrect(s[1..], c);
        
        var fullSet := set i | 0 <= i < |s| && s[i] == c;
        var restSet := set i | 0 <= i < |s[1..]| && s[1..][i] == c;
        var shiftedSet := set i | 1 <= i < |s| && s[i] == c;
        
        if s[0] == c {
            assert fullSet == {0} + shiftedSet;
            assert 0 !in shiftedSet;
            assert |fullSet| == 1 + |shiftedSet|;
            assert |shiftedSet| == |restSet|;
            assert countChar(s, c) == 1 + countChar(s[1..], c);
            assert countCharIterative(s, c) == 1 + countCharIterative(s[1..], c);
        } else {
            assert fullSet == shiftedSet;
            assert |fullSet| == |shiftedSet|;
            assert |shiftedSet| == |restSet|;
            assert countChar(s, c) == countChar(s[1..], c);
            assert countCharIterative(s, c) == countCharIterative(s[1..], c);
        }
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

