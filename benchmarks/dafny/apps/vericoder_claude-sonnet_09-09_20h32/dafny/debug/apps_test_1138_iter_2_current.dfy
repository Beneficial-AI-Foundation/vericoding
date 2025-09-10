predicate ValidInput(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
}

function abs(x: int): int
    ensures abs(x) >= 0
    ensures abs(x) == x || abs(x) == -x
{
    if x >= 0 then x else -x
}

function countChar(s: string, c: char): int
    requires 0 <= |s|
    ensures 0 <= countChar(s, c) <= |s|
    ensures countChar(s, c) == countCharHelper(s, c, 0, 0)
{
    countCharHelper(s, c, 0, 0)
}

function countCharHelper(s: string, c: char, index: int, count: int): int
    requires 0 <= index <= |s|
    requires count >= 0
    requires count + (|s| - index) >= 0
    decreases |s| - index
    ensures countCharHelper(s, c, index, count) >= count
    ensures countCharHelper(s, c, index, count) <= count + (|s| - index)
{
    if index == |s| then count
    else if s[index] == c then countCharHelper(s, c, index + 1, count + 1)
    else countCharHelper(s, c, index + 1, count)
}

function countCharFromIndex(s: string, c: char, index: int): int
    requires 0 <= index <= |s|
    ensures 0 <= countCharFromIndex(s, c, index) <= |s| - index
    decreases |s| - index
{
    if index == |s| then 0
    else if s[index] == c then 1 + countCharFromIndex(s, c, index + 1)
    else countCharFromIndex(s, c, index + 1)
}

predicate CorrectResult(s: string, result: int) {
    (|s| % 2 != 0 ==> result == -1) &&
    (|s| % 2 == 0 ==> result >= 0) &&
    (|s| % 2 == 0 ==> result <= |s| / 2) &&
    (|s| % 2 == 0 ==> result == (abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D'))) / 2)
}

// <vc-helpers>
lemma CountCharEquivalence(s: string, c: char, index: int)
    requires 0 <= index <= |s|
    ensures countCharHelper(s, c, index, 0) == countCharFromIndex(s, c, index)
    decreases |s| - index
{
    if index == |s| {
        assert countCharHelper(s, c, index, 0) == 0;
        assert countCharFromIndex(s, c, index) == 0;
    } else if s[index] == c {
        CountCharEquivalence(s, c, index + 1);
        assert countCharHelper(s, c, index + 1, 0) == countCharFromIndex(s, c, index + 1);
    } else {
        CountCharEquivalence(s, c, index + 1);
    }
}

lemma CountCharFromIndexBounds(s: string, c: char, index: int)
    requires 0 <= index <= |s|
    ensures countCharFromIndex(s, c, index) >= 0
    ensures countCharFromIndex(s, c, index) <= |s| - index
{
}

lemma AbsSum(a: int, b: int, c: int, d: int)
    ensures abs(a - b) + abs(c - d) >= 0
{
}

lemma CountCharSum(s: string)
    requires ValidInput(s)
    ensures countChar(s, 'L') + countChar(s, 'R') + countChar(s, 'U') + countChar(s, 'D') == |s|
    decreases |s|
{
    if |s| == 0 {
        assert countChar(s, 'L') == 0;
        assert countChar(s, 'R') == 0;
        assert countChar(s, 'U') == 0;
        assert countChar(s, 'D') == 0;
    } else {
        var s' := s[1..];
        assert ValidInput(s');
        CountCharSum(s');
        
        if s[0] == 'L' {
            assert countChar(s, 'L') == 1 + countChar(s', 'L');
            assert countChar(s, 'R') == countChar(s', 'R');
            assert countChar(s, 'U') == countChar(s', 'U');
            assert countChar(s, 'D') == countChar(s', 'D');
        } else if s[0] == 'R' {
            assert countChar(s, 'L') == countChar(s', 'L');
            assert countChar(s, 'R') == 1 + countChar(s', 'R');
            assert countChar(s, 'U') == countChar(s', 'U');
            assert countChar(s, 'D') == countChar(s', 'D');
        } else if s[0] == 'U' {
            assert countChar(s, 'L') == countChar(s', 'L');
            assert countChar(s, 'R') == countChar(s', 'R');
            assert countChar(s, 'U') == 1 + countChar(s', 'U');
            assert countChar(s, 'D') == countChar(s', 'D');
        } else if s[0] == 'D' {
            assert countChar(s, 'L') == countChar(s', 'L');
            assert countChar(s, 'R') == countChar(s', 'R');
            assert countChar(s, 'U') == countChar(s', 'U');
            assert countChar(s, 'D') == 1 + countChar(s', 'D');
        }
    }
}

lemma ResultBound(s: string)
    requires ValidInput(s)
    requires |s| % 2 == 0
    ensures (abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D'))) / 2 <= |s| / 2
{
    CountCharSum(s);
    var horizDiff := abs(countChar(s, 'L') - countChar(s, 'R'));
    var vertDiff := abs(countChar(s, 'U') - countChar(s, 'D'));
    var horizSum := countChar(s, 'L') + countChar(s, 'R');
    var vertSum := countChar(s, 'U') + countChar(s, 'D');
    
    assert horizSum + vertSum == |s|;
    assert horizDiff <= horizSum;
    assert vertDiff <= vertSum;
    assert horizDiff + vertDiff <= horizSum + vertSum;
    assert horizDiff + vertDiff <= |s|;
    assert (horizDiff + vertDiff) / 2 <= |s| / 2;
}

lemma EvenLengthProperty(s: string)
    requires ValidInput(s)
    requires |s| % 2 == 0
    ensures (abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D'))) % 2 == 0
{
    CountCharSum(s);
    var totalMoves := countChar(s, 'L') + countChar(s, 'R') + countChar(s, 'U') + countChar(s, 'D');
    
    assert totalMoves == |s|;
    
    var horizDiff := abs(countChar(s, 'L') - countChar(s, 'R'));
    var vertDiff := abs(countChar(s, 'U') - countChar(s, 'D'));
    
    var horizSum := countChar(s, 'L') + countChar(s, 'R');
    var vertSum := countChar(s, 'U') + countChar(s, 'D');
    
    assert horizSum + vertSum == |s|;
    assert (horizSum + vertSum) % 2 == 0;
    
    if countChar(s, 'L') >= countChar(s, 'R') {
        assert horizDiff == countChar(s, 'L') - countChar(s, 'R');
    } else {
        assert horizDiff == countChar(s, 'R') - countChar(s, 'L');
    }
    
    if countChar(s, 'U') >= countChar(s, 'D') {
        assert vertDiff == countChar(s, 'U') - countChar(s, 'D');
    } else {
        assert vertDiff == countChar(s, 'D') - countChar(s, 'U');
    }
    
    assert (horizDiff + vertDiff) % 2 == 0;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures CorrectResult(s, result)
// </vc-spec>
// <vc-code>
{
    if |s| % 2 != 0 {
        result := -1;
        return;
    }
    
    var countL := countChar(s, 'L');
    var countR := countChar(s, 'R');
    var countU := countChar(s, 'U');
    var countD := countChar(s, 'D');
    
    var horizDiff := abs(countL - countR);
    var vertDiff := abs(countU - countD);
    
    EvenLengthProperty(s);
    ResultBound(s);
    
    result := (horizDiff + vertDiff) / 2;
}
// </vc-code>

