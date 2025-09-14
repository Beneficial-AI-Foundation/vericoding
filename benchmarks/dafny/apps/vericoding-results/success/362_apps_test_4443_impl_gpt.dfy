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
lemma NextCharInRange(c: char)
  requires 'a' <= c <= 'y'
  ensures 'b' <= NextChar(c) <= 'z'
{
  assert (NextChar(c) as int) == (c as int) + 1;
  assert ('b' as int) == ('a' as int) + 1;
  assert ('z' as int) == ('y' as int) + 1;
  assert ('a' as int) <= (c as int) <= ('y' as int);
  assert ('b' as int) <= (NextChar(c) as int) <= ('z' as int);
  assert 'b' <= NextChar(c) <= 'z';
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
  NextCharInRange(input[0]);
  var s1 := " "[0 := c];
  assert |s1| == 1 && s1[0] == c;
  output := s1 + "\n";
  assert |"\n"| == 1 && "\n"[0] == '\n';
  assert |output| == 2;
  assert output[0] == c;
  assert output[1] == '\n';
  assert 'b' <= NextChar(input[0]) <= 'z';
}
// </vc-code>

