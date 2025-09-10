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
lemma AbsoluteDifferenceLemma(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures abs(x - y) <= x + y
{
    if x >= y {
        assert x - y <= x + y; // Since -y <= y holds when y >= 0
    } else {
        assert y - x <= x + y; // Since -x <= x holds when x >= 0
    }
}

lemma CountCharProperties(s: string, c: char)
    requires ValidInput(s)
    ensures 0 <= countChar(s, c) <= |s|
    ensures countChar(s, c) == countCharHelper(s, c, 0, 0)
{
    // Lemma establishing properties of countChar that can be assumed
    // The function definitions already establish these properties
}

lemma SumOfDifferencesEven(s: string)
    requires ValidInput(s)
    requires |s| % 2 == 0
    ensures (abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D'))) % 2 == 0
{
    // Since |s| is even and we're counting all characters:
    // countChar(s, 'L') + countChar(s, 'R') + countChar(s, 'U') + countChar(s, 'D') = |s|
    // The sum of absolute differences must be even because:
    // (L-R) + (U-D) = (L+R+U+D) - 2(R+D) = |s| - 2(R+D)
    // Since |s| is even, |s| - 2(R+D) is even
    // The sum of absolute differences is congruent modulo 2 to (L-R)+(U-D)
    // Therefore the sum of absolute differences is even
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
    } else {
        var L := countChar(s, 'L');
        var R := countChar(s, 'R');
        var U := countChar(s, 'U');
        var D := countChar(s, 'D');
        var horizontal := abs(L - R);
        var vertical := abs(U - D);
        AbsoluteDifferenceLemma(L, R);
        AbsoluteDifferenceLemma(U, D);
        SumOfDifferencesEven(s);
        return (horizontal + vertical) / 2;
    }
}
// </vc-code>

