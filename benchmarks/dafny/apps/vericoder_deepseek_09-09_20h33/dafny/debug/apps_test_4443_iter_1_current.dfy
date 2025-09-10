predicate ValidInput(input: string)
{
    |input| > 0 && 'a' <= input[0] <= 'y'
}

function NextChar(c: char): char
    requires 'a' <= c <= 'y'
{
    (c as int + 1) as char
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    |output| == 2 &&
    output[0] == NextChar(input[0]) &&
    output[1] == '\n' &&
    'b' <= output[0] <= 'z'
}

// <vc-helpers>
lemma NextCharRange(c: char)
  requires 'a' <= c <= 'y'
  ensures 'b' <= NextChar(c) <= 'z'
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(input, output)
// </vc-spec>
// <vc-code>
{
  var c := input[0];
  var next := NextChar(c);
  var result := new string[2];
  result[0] := next;
  result[1] := '\n';
  output := result;
}
// </vc-code>

