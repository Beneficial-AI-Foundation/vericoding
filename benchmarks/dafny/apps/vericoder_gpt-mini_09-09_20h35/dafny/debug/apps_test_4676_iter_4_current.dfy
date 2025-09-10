predicate ValidInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 &&
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    (a == b || a == b + 1) &&
    (a > 0 || b == 0)
}

function GetO(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[0]
}

function GetE(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[1]
}

function CorrectResult(input: string): string
    requires ValidInput(input)
{
    var O := GetO(input);
    var E := GetE(input);
    var a := |O|;
    var b := |E|;
    if a == b then
        InterleaveEqual(O, E)
    else
        InterleaveUnequal(O, E)
}

function InterleaveEqual(O: string, E: string): string
    requires |O| == |E|
{
    if |O| == 0 then ""
    else [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
}

function InterleaveUnequal(O: string, E: string): string
    requires |O| == |E| + 1
{
    if |E| == 0 then O
    else [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..])
}

// <vc-helpers>
function index_first(s: string, sep: char) returns (r: nat)
  requires exists i :: 0 <= i < |s| && s[i] == sep
  ensures 0 <= r < |s| && s[r] == sep && (forall j :: 0 <= j < r ==> s[j] != sep)
  decreases |s|
{
  if s[0] == sep then 0 else 1 + index_first(s[1..], sep)
}

function split(s: string, sep: char): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else if exists i :: 0 <= i < |s| && s[i] == sep then
    var i0 := index_first(s, sep);
    [s[0..i0]] + split(s[i0 + 1..], sep)
  else
    [s]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == CorrectResult(input)
// </vc-spec>
// <vc-code>
{
  result := CorrectResult(input);
}
// </vc-code>

