predicate ValidInput(input: string)
{
    |input| > 0 && exists i :: 0 <= i < |input| && input[i] == '\n'
}

predicate ValidCommandInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0])
}

function ExtractN(input: string): int
    requires ValidCommandInput(input)
{
    var lines := split(input, '\n');
    parseInteger(lines[0])
}

predicate CorrectOutput(input: string, result: string)
{
    ValidCommandInput(input) ==> 
        result == intToString(ExtractN(input) + 1) + "\n"
}

// <vc-helpers>
function split(s: seq<char>, sep: char): seq<seq<char>> 
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result|-1 ==> sep !in result[i]
    ensures forall c :: c in s ==> if c != sep then exists i :: c in result[i] else true
    decreases |s|
{
    if |s| == 0 then [[]]
    else if s[0] == sep then [[]] + split(s[1..], sep)
    else var prefix := s[..next(s, sep)];
         [prefix] + split(s[|prefix|..], sep)
}

function next(s: seq<char>, c: char): nat
    ensures 0 <= result <= |s|
    ensures forall i :: 0 <= i < result ==> s[i] != c
    ensures result == |s| || s[result] == c
{
    if |s| == 0 then 0
    else if s[0] == c then 0
    else 1 + next(s[1..], c)
}

predicate charIsDigit(c: char)
{
    '0' <= c <= '9'
}

predicate isValidInteger(s: seq<char>)
{
    |s| > 0 && forall c :: c in s ==> charIsDigit(c) && s[0] != '0'
}

function parseInteger(s: seq<char>): int
    requires isValidInteger(s)
    ensures parseInteger(s) >= 0
    decreases |s|
{
    if |s| == 1 then s[0] as int - '0' as int
    else 10 * parseInteger(s[..|s|-1]) + (s[|s|-1] as int - '0' as int)
}

function intToString(n: int): seq<char>
    requires n >= 0
    decreases n
{
    if n == 0 then "0"
    else (var d := n % 10; if n < 10 then [char(48 + d)] else intToString(n / 10) + [char(48 + d)])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{	
	if ValidCommandInput(input) {
		var n := ExtractN(input);
		result := intToString(n + 1) + "\n";
	} else {
		result := "";
	}
}
// </vc-code>

