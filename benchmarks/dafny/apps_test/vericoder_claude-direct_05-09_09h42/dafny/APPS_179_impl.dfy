// ======= TASK =======
// Count the number of permutations of size n where element x is placed at position pos
// and a specific binary search algorithm returns true when searching for x.
// The binary search repeatedly splits the search space and checks if middle <= x.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int, x: int, pos: int)
{
    n >= 1 && x >= 1 && x <= n && pos >= 0 && pos < n
}

function BinarySearchPositions(n: int, pos: int): (int, int)
    requires n > 0 && 0 <= pos < n
{
    var (chk1, chk_r) := BinarySearchHelper(n, pos, 0, n, 0, 0);
    (chk1, chk_r)
}

function BinarySearchHelper(n: int, pos: int, left: int, right: int, chk1: int, chk_r: int): (int, int)
    requires n > 0 && 0 <= pos < n
    requires 0 <= left <= right <= n
    requires chk1 >= 0 && chk_r >= 0
    decreases right - left
{
    if left >= right then (chk1, chk_r)
    else
        var middle := (left + right) / 2;
        if middle <= pos then
            var newChk1 := if middle < pos then chk1 + 1 else chk1;
            BinarySearchHelper(n, pos, middle + 1, right, newChk1, chk_r)
        else
            BinarySearchHelper(n, pos, left, middle, chk1, chk_r + 1)
}

predicate ValidConfiguration(n: int, x: int, pos: int)
    requires ValidInput(n, x, pos)
{
    var (chk1, chk_r) := BinarySearchPositions(n, pos);
    chk1 <= x - 1 && chk_r <= n - x && n - chk1 - chk_r - 1 >= 0
}

// <vc-helpers>
function f(n: int, cnt: int): int
    requires n >= 0 && cnt >= 0 && cnt <= n
{
    if cnt <= 0 then 1
    else if n <= 0 then 1
    else
        var MOD := 1000000007;
        fHelper(n, cnt, 1, MOD)
}

function fHelper(n: int, cnt: int, acc: int, MOD: int): int
    requires n >= 0 && cnt >= 0 && acc >= 0 && MOD > 1
    requires cnt <= n
    decreases cnt
{
    if cnt <= 0 then if acc == 0 then 1 else acc
    else if n <= 0 then if acc == 0 then 1 else acc
    else 
        var newAcc := (acc * n) % MOD;
        fHelper(n - 1, cnt - 1, if newAcc == 0 then 1 else newAcc, MOD)
}

function Split(s: string, delimiter: char): seq<string>
    requires |s| >= 0
    ensures |Split(s, delimiter)| >= 1
    ensures |s| == 0 ==> Split(s, delimiter) == [""]
{
    if |s| == 0 then [""]
    else 
        var result := SplitHelper(s, delimiter, 0, "");
        if |result| == 0 then [""] else result
}

function SplitHelper(s: string, delimiter: char, index: int, current: string): seq<string>
    requires 0 <= index <= |s|
    ensures |SplitHelper(s, delimiter, index, current)| >= 0
    decreases |s| - index
{
    if index >= |s| then
        if |current| > 0 then [current] else []
    else if s[index] == delimiter then
        if |current| > 0 then [current] + SplitHelper(s, delimiter, index + 1, "")
        else SplitHelper(s, delimiter, index + 1, "")
    else
        SplitHelper(s, delimiter, index + 1, current + [s[index]])
}

function StringToInt(s: string): int
    requires |s| >= 0
    ensures |s| == 0 ==> StringToInt(s) == 0
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
    requires |s| >= 0
    ensures StringToIntHelper(s) >= 0
    ensures |s| == 0 ==> StringToIntHelper(s) == 0
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int
        else 0
    else
        if '0' <= s[0] <= '9' then
            (s[0] as int - '0' as int) * Pow10(|s| - 1) + StringToIntHelper(s[1..])
        else 0
}

function Pow10(n: int): int
    requires n >= 0
    ensures Pow10(n) >= 1
    ensures n == 0 ==> Pow10(n) == 1
{
    if n <= 0 then 1
    else 10 * Pow10(n - 1)
}

function IntToString(n: int): string
    ensures |IntToString(n)| >= 1
    ensures n == 0 ==> IntToString(n) == "0"
    ensures n < 0 ==> IntToString(n) == "-" + IntToStringHelper(-n)
    ensures n > 0 ==> IntToString(n) == IntToStringHelper(n)
    ensures forall i :: 0 <= i < |IntToString(n)| ==> (IntToString(n)[i] == '-' || ('0' <= IntToString(n)[i] <= '9'))
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
    ensures n == 0 ==> IntToStringHelper(n) == ""
    ensures n > 0 ==> |IntToStringHelper(n)| >= 1
    ensures forall i :: 0 <= i < |IntToStringHelper(n)| ==> '0' <= IntToStringHelper(n)[i] <= '9'
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [((n % 10) + ('0' as int)) as char]
}

lemma BinarySearchEquivalence(n: int, pos: int, left: int, right: int, chk1_init: int, chk_r_init: int)
    requires n > 0 && 0 <= pos < n
    requires 0 <= left <= right <= n
    requires chk1_init >= 0 && chk_r_init >= 0
    ensures BinarySearchHelper(n, pos, left, right, chk1_init, chk_r_init) == 
            BinarySearchLoop(n, pos, left, right, chk1_init, chk_r_init)
    decreases right - left
{
    if left >= right {
    } else {
        var middle := (left + right) / 2;
        if middle <= pos {
            var newChk1 := if middle < pos then chk1_init + 1 else chk1_init;
            BinarySearchEquivalence(n, pos, middle + 1, right, newChk1, chk_r_init);
        } else {
            BinarySearchEquivalence(n, pos, left, middle, chk1_init, chk_r_init + 1);
        }
    }
}

function BinarySearchLoop(n: int, pos: int, left: int, right: int, chk1: int, chk_r: int): (int, int)
    requires n > 0 && 0 <= pos < n
    requires 0 <= left <= right <= n
    requires chk1 >= 0 && chk_r >= 0
    decreases right - left
{
    if left >= right then (chk1, chk_r)
    else
        var middle := (left + right) / 2;
        if middle <= pos then
            var newChk1 := if middle < pos then chk1 + 1 else chk1;
            BinarySearchLoop(n, pos, middle + 1, right, newChk1, chk_r)
        else
            BinarySearchLoop(n, pos, left, middle, chk1, chk_r + 1)
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == '\n'
    requires var lines := Split(input, '\n');
             |lines| > 0 && |lines[0]| > 0
    requires var lines := Split(input, '\n');
             var parts := Split(lines[0], ' ');
             |parts| >= 3
    ensures |output| > 0
    ensures (output == "0" || (|output| > 0 && forall i :: 0 <= i < |output| ==> '0' <= output[i] <= '9'))
// </vc-spec>
// <vc-code>
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    var n := StringToInt(parts[0]);
    var x := StringToInt(parts[1]);
    var pos := StringToInt(parts[2]);

    var MOD := 1000000007;

    if !ValidInput(n, x, pos) {
        output := "0";
        return;
    }

    var chk1 := 0;
    var chk_r := 0;
    var left := 0;
    var right := n;
    
    while left < right 
        invariant 0 <= left <= right <= n
        invariant chk1 >= 0 && chk_r >= 0
        invariant (chk1, chk_r) == BinarySearchLoop(n, pos, left, right, chk1, chk_r)
        decreases right - left
    {
        var middle := (left + right) / 2;
        if middle <= pos {
            if middle < pos {
                chk1 := chk1 + 1;
            }
            left := middle + 1;
        } else {
            chk_r := chk_r + 1;
            right := middle;
        }
    }

    var (expected_chk1, expected_chk_r) := BinarySearchPositions(n, pos);
    assert (chk1, chk_r) == (expected_chk1, expected_chk_r);

    if chk1 > x - 1 || chk_r > n - x {
        output := "0";
    } else {
        var rest := n - chk1 - chk_r - 1;
        if rest < 0 {
            output := "0";
        } else {
            var f1 := f(x - 1, chk1);
            var f2 := f(n - x, chk_r);
            var f3 := f(rest, rest);
            var result := (((f1 * f2) % MOD) * f3) % MOD;
            output := IntToString(result);
        }
    }
}
// </vc-code>

