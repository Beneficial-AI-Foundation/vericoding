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
  var ci := c as int;
  assert (NextChar(c) as int) == ci + 1;
  assert 'a' as int <= ci && ci <= 'y' as int;
  assert 'b' as int <= ci + 1 && ci + 1 <= 'z' as int;
  assert 'b' as int <= (NextChar(c) as int) && (NextChar(c) as int) <= 'z' as int;
  // Conclude the char-range fact from the integer-range fact
  assert 'b' <= NextChar(c) && NextChar(c) <= 'z';
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
  output := [c, '\n'];
  // Prove the required properties
  NextCharRange(input[0]);
  assert |output| == 2;
  assert output[0] == c;
  assert output[1] == '\n';
}
// </vc-code>

