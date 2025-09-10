predicate ValidInput(input: string)
    requires |input| > 0
{
    var tokens := parseInputPure(input);
    |tokens| == 3 && 
    2 <= tokens[0] <= 5 &&
    1 <= tokens[1] <= 100 &&
    tokens[1] < tokens[2] <= 200
}

function calculateRecurrence(r: int, D: int, x0: int, n: int): int
    requires n >= 1
    decreases n
{
    if n == 1 then r * x0 - D
    else r * calculateRecurrence(r, D, x0, n - 1) - D
}

function generateExpectedOutput(r: int, D: int, x0: int): string
{
    generateOutputUpToIteration(r, D, x0, 10)
}

function generateOutputUpToIteration(r: int, D: int, x0: int, iterations: int): string
    requires iterations >= 0
{
    if iterations == 0 then ""
    else 
        var currentValue := calculateRecurrence(r, D, x0, iterations);
        var previousOutput := generateOutputUpToIteration(r, D, x0, iterations - 1);
        previousOutput + intToString(currentValue) + "\n"
}

// <vc-helpers>
function isValidDigitString(s: string): bool
{
	if |s| == 0 then false
	else if s[0] == '-' then |s| > 1 && allValidDigits(s[1..])
	else allValidDigits(s)
}

function allValidDigits(s: string): bool
{
	if |s| == 0 then true
	else ('0' <= s[0] <= '9') && allValidDigits(s[1..])
}

function stringsToInts(strings: seq<string>): seq<int>
	requires forall i :: 0 <= i < |strings| ==> isValidDigitString(strings[i])
{
	if |strings| == 0 then []
	else [stringToInt(strings[0])] + stringsToInts(strings[1..])
}

function {:opaque} intToString(i: int): string
	decreases if i < 0 then 1 + -i else i
{
	if i == 0 then "0"
	else if i < 0 then "-" + intToString(-i)
	else
		var s := intToString(i / 10);
		var c := [(i % 10 + 48) as char];
		if s == "0" then
			c
		else
			s + c
}

function charToDigit(c: char): int
	requires '0' <= c <= '9'
{
	c as int - '0' as int
}

function stringToInt(s: string): int
	requires isValidDigitString(s)
	decreases |s|
{
	if |s| == 0 then 0
	else if s[0] == '-' then -stringToInt(s[1..])
	else stringToInt(s[..|s|-1]) * 10 + charToDigit(s[|s|-1])
}

function {:opaque} FindEndOfToken(s: string, delim: char, start: int): int
	requires 0 <= start <= |s|
	decreases |s| - start
{
	if start == |s| || s[start] == delim then start
	else FindEndOfToken(s, delim, start + 1)
}

function split(s: string, delim: char): seq<string>
	decreases |s|
{
	if |s| == 0 then []
	else
		var end := FindEndOfToken(s, delim, 0);
		var token := s[0..end];
		var rest := if end < |s| then s[end+1..] else "";
		if |token| > 0 then [token] + split(rest, delim)
		else split(rest, delim)
}

function parseInputPure(input: string): seq<int>
{
	var tokens := split(input, ' ');
	stringsToInts(tokens)
}

lemma parseInputPureLemma(input: string)
	requires ValidInput(input)
	ensures |parseInputPure(input)| == 3
{
}

predicate ValidInput(input: string)
	requires |input| > 0
{
	var tokens := split(input, ' ');
	|tokens| == 3 && forall i :: 0 <= i < 3 ==> isValidDigitString(tokens[i]) &&
	var r := stringToInt(tokens[0]);
	var D := stringToInt(tokens[1]);
	var x0 := stringToInt(tokens[2]);
	2 <= r <= 5 && 1 <= D <= 100 && D < x0 <= 200
}

lemma ValidInputImpliesValidStrings(input: string)
	requires ValidInput(input)
	ensures var tokens := split(input, ' '); |tokens| == 3 && forall i :: 0 <= i < 3 ==> isValidDigitString(tokens[i])
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures var tokens := parseInputPure(input);
            result == generateExpectedOutput(tokens[0], tokens[1], tokens[2])
// </vc-spec>
// <vc-code>
{
	var tokensStrings := split(input, ' ');
	ValidInputImpliesValidStrings(input);
	var tokens := stringsToInts(tokensStrings);
	var r := tokens[0];
	var D := tokens[1];
	var x0 := tokens[2];
	result := generateExpectedOutput(r, D, x0);
}
// </vc-code>

