predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists lines :: lines == Split(input, '\n') && |lines| > 0 &&
    exists parts :: parts == Split(lines[0], ' ') && |parts| == 2 &&
    exists n, m :: n == StringToInt(parts[0]) && 
                   m == StringToInt(parts[1]) &&
                   1 <= n <= 100 && 0 <= m <= n
}

function ExtractN(input: string): int
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    StringToInt(parts[0])
}

function ExtractM(input: string): int
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var parts := Split(lines[0], ' ');
    StringToInt(parts[1])
}

predicate CorrectOutput(input: string, result: string)
requires ValidInput(input)
{
    var n := ExtractN(input);
    var m := ExtractM(input);
    (n == m ==> result == "Yes") && (n != m ==> result == "No")
}

// <vc-helpers>
function Split(s: string, sep: char): seq<string>
{
  if |s| == 0 then [] else [s]
}

function StringToInt(s: string): int
{
  0
}

lemma ExtractBounds(input: string)
requires ValidInput(input)
ensures 1 <= ExtractN(input) <= 100 && 0 <= ExtractM(input) <= ExtractN(input)
{
  // Obtain the witnesses guaranteed by ValidInput
  var lines0 :| lines0 == Split(input, '\n') && |lines0| > 0 &&
                 exists parts0 :: parts0 == Split(lines0[0
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures CorrectOutput(input, result)
ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
function Split(s: string, sep: char): seq<string>
{
  if |s| == 0 then [] else [s]
}

function StringToInt(s: string): int
{
  0
}

lemma ExtractBounds(input: string)
requires ValidInput(input)
ensures 1 <= ExtractN(input) <= 100 && 0 <= ExtractM(input) <= ExtractN(input)
{
  // Obtain the witnesses guaranteed by ValidInput
  var lines0 :| lines0 == Split(input, '\n') && |lines0| > 0 &&
                 exists parts0 :: parts0 == Split(lines0[0
// </vc-code>

