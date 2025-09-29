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
lemma CountCharProperties(s: string, c: char)
    ensures countChar(s, c) == countCharFromIndex(s, c, 0)
{
    var count := countChar(s, c);
    var countFrom := countCharFromIndex(s, c, 0);
    assert count == countCharHelper(s, c, 0, 0);
    CountCharHelperEquivalence(s, c, 0, 0);
}

lemma CountCharHelperEquivalence(s: string, c: char, index: int, count: int)
    requires 0 <= index <= |s|
    requires count >= 0
    ensures countCharHelper(s, c, index, count) == count + countCharFromIndex(s, c, index)
    decreases |s| - index
{
    if index == |s| {
        assert countCharHelper(s, c, index, count) == count;
        assert countCharFromIndex(s, c, index) == 0;
    } else if s[index] == c {
        CountCharHelperEquivalence(s, c, index + 1, count + 1);
    } else {
        CountCharHelperEquivalence(s, c, index + 1, count);
    }
}

lemma CountCharTail(s: string, c: char)
    requires |s| > 0
    ensures countChar(s[1..], c) == countCharFromIndex(s, c, 1)
{
    var s' := s[1..];
    assert countChar(s', c) == countCharHelper(s', c, 0, 0);
    
    // First prove that countCharHelper(s', c, 0, 0) relates to countCharFromIndex(s', c, 0)
    CountCharHelperEquivalence(s', c, 0, 0);
    assert countCharHelper(s', c, 0, 0) == countCharFromIndex(s', c, 0);
    
    // Now prove that countCharFromIndex(s', c, 0) == countCharFromIndex(s, c, 1)
    CountCharFromIndexTail(s, c);
    assert countCharFromIndex(s', c, 0) == countCharFromIndex(s, c, 1);
    
    // Chain the equalities
    assert countChar(s', c) == countCharFromIndex(s, c, 1);
}

lemma CountCharFromIndexTail(s: string, c: char)
    requires |s| > 0
    ensures countCharFromIndex(s[1..], c, 0) == countCharFromIndex(s, c, 1)
{
    var s' := s[1..];
    CountCharFromIndexTailHelper(s, s', c, 0);
}

lemma CountCharFromIndexTailHelper(s: string, s': string, c: char, index: int)
    requires |s| > 0
    requires s' == s[1..]
    requires 0 <= index <= |s'|
    ensures countCharFromIndex(s', c, index) == countCharFromIndex(s, c, index + 1)
    decreases |s'| - index
{
    if index == |s'| {
        assert index + 1 == |s|;
        assert countCharFromIndex(s', c, index) == 0;
        assert countCharFromIndex(s, c, index + 1) == 0;
    } else {
        assert s'[index] == s[index + 1];
        if s'[index] == c {
            assert countCharFromIndex(s', c, index) == 1 + countCharFromIndex(s', c, index + 1);
            assert countCharFromIndex(s, c, index + 1) == 1 + countCharFromIndex(s, c, index + 2);
            CountCharFromIndexTailHelper(s, s', c, index + 1);
            assert countCharFromIndex(s', c, index + 1) == countCharFromIndex(s, c, index + 2);
        } else {
            assert countCharFromIndex(s', c, index) == countCharFromIndex(s', c, index + 1);
            assert countCharFromIndex(s, c, index + 1) == countCharFromIndex(s, c, index + 2);
            CountCharFromIndexTailHelper(s, s', c, index + 1);
            assert countCharFromIndex(s', c, index + 1) == countCharFromIndex(s, c, index + 2);
        }
    }
}

lemma CountCharFirstChar(s: string, c: char)
    requires |s| > 0
    ensures s[0] == c ==> countChar(s, c) == 1 + countChar(s[1..], c)
    ensures s[0] != c ==> countChar(s, c) == countChar(s[1..], c)
{
    CountCharProperties(s, c);
    assert countChar(s, c) == countCharFromIndex(s, c, 0);
    
    if s[0] == c {
        assert countCharFromIndex(s, c, 0) == 1 + countCharFromIndex(s, c, 1);
    } else {
        assert countCharFromIndex(s, c, 0) == countCharFromIndex(s, c, 1);
    }
    
    CountCharTail(s, c);
    assert countChar(s[1..], c) == countCharFromIndex(s, c, 1);
}

lemma CountAllChars(s: string)
    requires ValidInput(s)
    ensures countChar(s, 'L') + countChar(s, 'R') + countChar(s, 'U') + countChar(s, 'D') == |s|
{
    if |s| == 0 {
        return;
    }
    
    var s' := s[1..];
    assert ValidInput(s');
    CountAllChars(s');
    
    var c := s[0];
    assert c == 'L' || c == 'R' || c == 'U' || c == 'D' by {
        assert ValidInput(s);
    }
    
    CountCharFirstChar(s, 'L');
    CountCharFirstChar(s, 'R');
    CountCharFirstChar(s, 'U');
    CountCharFirstChar(s, 'D');
    
    if c == 'L' {
        assert countChar(s, 'L') == 1 + countChar(s', 'L');
        assert countChar(s, 'R') == countChar(s', 'R');
        assert countChar(s, 'U') == countChar(s', 'U');
        assert countChar(s, 'D') == countChar(s', 'D');
    } else if c == 'R' {
        assert countChar(s, 'L') == countChar(s', 'L');
        assert countChar(s, 'R') == 1 + countChar(s', 'R');
        assert countChar(s, 'U') == countChar(s', 'U');
        assert countChar(s, 'D') == countChar(s', 'D');
    } else if c == 'U' {
        assert countChar(s, 'L') == countChar(s', 'L');
        assert countChar(s, 'R') == countChar(s', 'R');
        assert countChar(s, 'U') == 1 + countChar(s', 'U');
        assert countChar(s, 'D') == countChar(s', 'D');
    } else {
        assert c == 'D';
        assert countChar(s, 'L') == countChar(s', 'L');
        assert countChar(s, 'R') == countChar(s', 'R');
        assert countChar(s, 'U') == countChar(s', 'U');
        assert countChar(s, 'D') == 1 + countChar(s', 'D');
    }
}

lemma DiffBound(s: string)
    requires ValidInput(s)
    ensures abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D')) <= |s|
{
    CountAllChars(s);
    var countL := countChar(s, 'L');
    var countR := countChar(s, 'R');
    var countU := countChar(s, 'U');
    var countD := countChar(s, 'D');
    
    assert countL + countR + countU + countD == |s|;
    
    // abs(countL - countR) <= countL + countR
    assert abs(countL - countR) <= countL + countR;
    
    // abs(countU - countD) <= countU + countD
    assert abs(countU - countD) <= countU + countD;
    
    // Therefore: abs(countL - countR) + abs(countU - countD) <= (countL + countR) + (countU + countD) == |s|
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
        return -1;
    }
    
    var countL := countChar(s, 'L');
    var countR := countChar(s, 'R');
    var countU := countChar(s, 'U');
    var countD := countChar(s, 'D');
    
    var diffLR := abs(countL - countR);
    var diffUD := abs(countU - countD);
    
    DiffBound(s);
    assert diffLR + diffUD <= |s|;
    
    result := (diffLR + diffUD) / 2;
    
    assert result <= |s| / 2;
}
// </vc-code>

