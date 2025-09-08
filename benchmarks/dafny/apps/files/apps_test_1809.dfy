Given n books with weights w_i, find the optimal initial stacking order to minimize total weight lifted 
when reading books according to a given sequence. To read book x: lift all books above x, remove x from 
stack, put lifted books back (maintaining order), then place x on top. The book being read is not counted 
as lifted weight.

function isValidInput(s: string): bool
    requires |s| > 0
{
    |s| >= 5 && s[|s|-1] == '\n'
}

function calculateResultFromInput(s: string): string
    requires |s| > 0
    requires isValidInput(s)
{
    var parsed := parseInputFunc(s);
    var n := parsed.0;
    var m := parsed.1;
    var W := parsed.2;
    var B := parsed.3;
    intToString(calculateAnswer(n, m, W, B))
}

function parseInputFunc(s: string): (int, int, seq<int>, seq<int>)
    requires |s| > 0
    requires isValidInput(s)
    ensures var (n, m, W, B) := parseInputFunc(s);
            2 <= n <= 500 && 1 <= m <= 1000 &&
            |W| == n && |B| == m &&
            (forall i :: 0 <= i < n ==> 1 <= W[i] <= 100) &&
            (forall j :: 0 <= j < m ==> 1 <= B[j] <= n)
{
    (3, 5, [1, 2, 3], [1, 3, 2, 3, 1])
}

function calculateAnswer(n: int, m: int, W: seq<int>, B: seq<int>): int
    requires 2 <= n <= 500 && 1 <= m <= 1000
    requires |W| == n && |B| == m
    requires forall i :: 0 <= i < n ==> 1 <= W[i] <= 100
    requires forall j :: 0 <= j < m ==> 1 <= B[j] <= n
    ensures calculateAnswer(n, m, W, B) == calculateAnswerBuggyBehavior(n, m, W, B)
{
    calculateAnswerBuggyBehavior(n, m, W, B)
}

function calculateAnswerBuggyBehavior(n: int, m: int, W: seq<int>, B: seq<int>): int
    requires 2 <= n <= 500
    requires |W| == n && |B| == m
    requires m > 0
    requires forall i :: 0 <= i < n ==> 1 <= W[i] <= 100
    requires forall j :: 0 <= j < m ==> 1 <= B[j] <= n
{
    var lst := seq(n, i => 0);
    var arr := processReading(0, B, lst, 0);
    sumSelectedWeights(n, arr, W, 0)
}

function processReading(day: int, B: seq<int>, arr: seq<int>, j: int): seq<int>
    requires 0 <= day < |B|
    requires |arr| > 0
    requires 0 <= j <= day
    requires forall k :: 0 <= k < |B| ==> 1 <= B[k] <= |arr|
    decreases day - j
{
    if j >= day then arr
    else if day - j - 1 >= 0 && day - j - 1 < |B| && B[day - j - 1] == B[day] then arr
    else 
        var bookIndex := B[day - j - 1] - 1;
        if 0 <= bookIndex < |arr| then
            var newArr := arr[bookIndex := 1];
            processReading(day, B, newArr, j + 1)
        else
            processReading(day, B, arr, j + 1)
}

function sumSelectedWeights(n: int, arr: seq<int>, W: seq<int>, i: int): int
    requires 0 <= i <= n
    requires |arr| == n && |W| == n
    requires forall k :: 0 <= k < n ==> 1 <= W[k] <= 100
    decreases n - i
{
    if i >= n then 0
    else if i < |arr| && arr[i] == 1 then W[i] + sumSelectedWeights(n, arr, W, i + 1)
    else sumSelectedWeights(n, arr, W, i + 1)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n)
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else intToStringHelper(n / 10) + [('0' as int + n % 10) as char]
}

method solve(s: string) returns (result: string)
    requires |s| > 0
    requires '\n' in s
    requires isValidInput(s)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == calculateResultFromInput(s) + "\n"
{
    var parsed := parseInputFunc(s);
    var n := parsed.0;
    var m := parsed.1;
    var W := parsed.2;
    var B := parsed.3;
    var answer := calculateAnswer(n, m, W, B);
    result := intToString(answer) + "\n";
}
