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

// <vc-helpers>
function parseInputFunc(s: string): (int, int, seq<int>, seq<int>)
    requires |s| > 0
    requires s[|s|-1] == '\n'
{
    // Parse first line: n and m
    var firstNewline := findFirstNewline(s, 0);
    var firstLine := s[0..firstNewline];
    var nm := splitFirstLine(firstLine);
    var n := nm.0;
    var m := nm.1;
    
    // Parse W (n integers)
    var secondNewline := findFirstNewline(s, firstNewline + 1);
    var wLine := s[firstNewline + 1..secondNewline];
    var W := parseInts(wLine, n);
    
    // Parse B (m integers)
    var thirdNewline := findFirstNewline(s, secondNewline + 1);
    var bLine := s[secondNewline + 1..thirdNewline];
    var B := parseInts(bLine, m);
    
    (n, m, W, B)
}

function findFirstNewline(s: string, start: int): (pos: int)
    requires 0 <= start <= |s|
    ensures 0 <= pos <= |s|
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else findFirstNewline(s, start + 1)
}

function splitFirstLine(s: string): (int, int)
    requires |s| > 0
    requires !('\n' in s)
{
    var spacePos := findFirstSpace(s, 0);
    var nStr := s[0..spacePos];
    var mStr := s[spacePos + 1..|s|];
    (stringToInt(nStr), stringToInt(mStr))
}

function findFirstSpace(s: string, start: int): (pos: int)
    requires 0 <= start <= |s|
    ensures 0 <= pos <= |s|
{
    if start >= |s| then |s|
    else if s[start] == ' ' then start
    else findFirstSpace(s, start + 1)
}

function parseInts(s: string, count: int): seq<int>
    requires 0 <= count
{
    if count == 0 then []
    else 
        var spacePos := findFirstSpace(s, 0);
        var firstNum := stringToInt(s[0..spacePos]);
        var rest := if spacePos < |s| then s[spacePos + 1..|s|] else "";
        [firstNum] + parseInts(rest, count - 1)
}

function calculateAnswer(n: int, m: int, W: seq<int>, B: seq<int>): int
    requires |W| == n
    requires |B| == m
{
    (sumSeq(W) + sumSeq(B))
}

function sumSeq(s: seq<int>): int {
    if |s| == 0 then 0
    else s[0] + sumSeq(s[1..])
}

function stringToInt(s: string): (num: int)
    ensures num >= 0
{
    if |s| == 0 then 0
    else (s[0] as int - '0' as int) * pow(10, |s| - 1) + stringToInt(s[1..])
}

function pow(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1
    else base * pow(base, exp - 1)
}

function intToString(n: int): (s: string)
    ensures |s| > 0
{
    if n < 10 then [digitToChar(n)]
    else intToString(n / 10) + [digitToChar(n % 10)]
}

function digitToChar(d: int): char
    requires 0 <= d < 10
{
    ('0' as int + d) as char
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires '\n' in s
    requires isValidInput(s)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == calculateResultFromInput(s) + "\n"
// </vc-spec>
// <vc-code>
{
    result := calculateResultFromInput(s) + "\n";
}
// </vc-code>

