// ======= TASK =======
// Given a 6-digit string, find the minimum number of digit replacements needed to make it "lucky". 
// A ticket is lucky when the sum of the first three digits equals the sum of the last three digits. 
// Each replacement can change any digit to any digit (0-9).

// ======= SPEC REQUIREMENTS =======
function parseDigits(s: string): seq<int>
    requires |s| == 6
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |parseDigits(s)| == 6
    ensures forall i :: 0 <= i < 6 ==> 0 <= parseDigits(s)[i] <= 9
{
    [s[0] as int - '0' as int, s[1] as int - '0' as int, s[2] as int - '0' as int,
     s[3] as int - '0' as int, s[4] as int - '0' as int, s[5] as int - '0' as int]
}

predicate isLucky(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
{
    digits[0] + digits[1] + digits[2] == digits[3] + digits[4] + digits[5]
}

predicate canMakeLuckyWith1Change(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
{
    exists i, j {:trigger digits[i := j]} :: 0 <= i < 6 && 0 <= j <= 9 && isLucky(digits[i := j])
}

predicate canMakeLuckyWith2Changes(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
{
    exists i, k, l, m {:trigger digits[i := l][k := m]} :: 0 <= i < 6 && 0 <= k < 6 && k != i && 0 <= l <= 9 && 0 <= m <= 9 && 
                        isLucky(digits[i := l][k := m])
}

// <vc-helpers>
lemma lemma_canMakeLuckyWith1Change_def(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
    ensures canMakeLuckyWith1Change(digits) <==> (exists i, j {:trigger digits[i := j]} :: 0 <= i < 6 && 0 <= j <= 9 && isLucky(digits[i := j]))
{
}

lemma lemma_canMakeLuckyWith2Changes_def(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
    ensures canMakeLuckyWith2Changes(digits) <==> (exists i, k, l, m {:trigger digits[i := l][k := m]} :: 0 <= i < 6 && 0 <= k < 6 && k != i && 0 <= l <= 9 && 0 <= m <= 9 && isLucky(digits[i := l][k := m]))
{
}

lemma lemma_not_canMakeLuckyWith1Change(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
    requires forall i, j {:trigger digits[i := j]} :: 0 <= i < 6 && 0 <= j <= 9 ==> !isLucky(digits[i := j])
    ensures !canMakeLuckyWith1Change(digits)
{
    lemma_canMakeLuckyWith1Change_def(digits);
}

lemma lemma_not_canMakeLuckyWith2Changes(digits: seq<int>)
    requires |digits| == 6
    requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
    requires forall i, k, l, m {:trigger digits[i := l][k := m]} :: 0 <= i < 6 && 0 <= k < 6 && k != i && 0 <= l <= 9 && 0 <= m <= 9 ==> !isLucky(digits[i := l][k := m])
    ensures !canMakeLuckyWith2Changes(digits)
{
    lemma_canMakeLuckyWith2Changes_def(digits);
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| >= 6
    requires forall i :: 0 <= i < 6 ==> '0' <= input[i] <= '9'
    ensures |output| == 1
    ensures output == "0" || output == "1" || output == "2" || output == "3"
    ensures output == "0" <==> isLucky(parseDigits(input[..6]))
    ensures output == "1" <==> (!isLucky(parseDigits(input[..6])) && canMakeLuckyWith1Change(parseDigits(input[..6])))
    ensures output == "2" <==> (!isLucky(parseDigits(input[..6])) && !canMakeLuckyWith1Change(parseDigits(input[..6])) && canMakeLuckyWith2Changes(parseDigits(input[..6])))
    ensures output == "3" <==> (!isLucky(parseDigits(input[..6])) && !canMakeLuckyWith1Change(parseDigits(input[..6])) && !canMakeLuckyWith2Changes(parseDigits(input[..6])))
// </vc-spec>
// <vc-code>
{
    var digits := parseDigits(input[..6]);

    if isLucky(digits) {
        return "0";
    }

    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant forall i', j' {:trigger digits[i' := j']} :: 0 <= i' < i && 0 <= j' <= 9 ==> !isLucky(digits[i' := j'])
    {
        var j := 0;
        while j < 10
            invariant 0 <= j <= 10
            invariant forall j' {:trigger digits[i := j']} :: 0 <= j' < j ==> !isLucky(digits[i := j'])
        {
            var newDigits := digits[i := j];
            if isLucky(newDigits) {
                return "1";
            }
            j := j + 1;
        }
        i := i + 1;
    }

    lemma_not_canMakeLuckyWith1Change(digits);

    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant forall i', k', l', m' {:trigger digits[i' := l'][k' := m']} :: 0 <= i' < i && 0 <= k' < 6 && k' != i' && 0 <= l' <= 9 && 0 <= m' <= 9 ==> !isLucky(digits[i' := l'][k' := m'])
    {
        var k := 0;
        while k < 6
            invariant 0 <= k <= 6
            invariant forall k', l', m' {:trigger digits[i := l'][k' := m']} :: 0 <= k' < k && k' != i && 0 <= l' <= 9 && 0 <= m' <= 9 ==> !isLucky(digits[i := l'][k' := m'])
        {
            if k != i {
                var l := 0;
                while l < 10
                    invariant 0 <= l <= 10
                    invariant forall l', m' {:trigger digits[i := l'][k := m']} :: 0 <= l' < l && 0 <= m' <= 9 ==> !isLucky(digits[i := l'][k := m'])
                {
                    var m := 0;
                    while m < 10
                        invariant 0 <= m <= 10
                        invariant forall m' {:trigger digits[i := l][k := m']} :: 0 <= m' < m ==> !isLucky(digits[i := l][k := m'])
                    {
                        var newDigits := digits[i := l][k := m];
                        if isLucky(newDigits) {
                            return "2";
                        }
                        m := m + 1;
                    }
                    l := l + 1;
                }
            }
            k := k + 1;
        }
        i := i + 1;
    }

    lemma_not_canMakeLuckyWith2Changes(digits);

    return "3";
}
// </vc-code>

