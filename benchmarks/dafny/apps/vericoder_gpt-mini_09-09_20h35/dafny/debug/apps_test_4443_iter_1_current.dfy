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
  // Use integer representation to reason about char bounds
  var ci := c as int;
  assert (NextChar(c) as int) == ci + 1;
  assert (int)('a') <= ci <= (int)('y');
  assert (int)('b') <= ci + 1 <= (int)('z');
  assert (int)('b') <= (NextChar(c) as int) <= (int)('z');
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(input, output)
// </vc-spec>
// <vc-code>
{
  var c := NextChar(input[0]);
  output := "" + c + '\n';
  // Prove the required properties
  NextCharRange(input[0]);
  assert |output| == 2;
  assert output[0] == c;
  assert output[1] == '\n';
}
// </vc-code>

