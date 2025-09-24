// <vc-preamble>
predicate ValidInput(input: string)
{
  |input| > 0 &&
  (exists i :: 0 <= i < |input| && input[i] == ' ') &&
  (forall c :: c in input ==> c in "0123456789 \n") &&
  input[|input|-1] == '\n'
}

predicate ValidOutput(output: string)
{
  |output| > 0 &&
  output[|output|-1] == '\n' &&
  (forall c :: c in output ==> c in "0123456789\n")
}

function parse_integers(input: string): (int, int)
  requires |input| > 0
  requires exists i :: 0 <= i < |input| && input[i] == ' '
  requires forall c :: c in input ==> c in "0123456789 \n"
  requires input[|input|-1] == '\n'
{
  (1, 1)
}

function gg(n: int, lol: int): int
  requires n >= 1 && lol >= 1
  ensures gg(n, lol) >= 0
  ensures lol > n ==> gg(n, lol) == 0
  ensures gg(n, lol) <= n
  decreases n, lol
{
  0
}

function nat_to_string(n: int): string
  requires n >= 0
  ensures |nat_to_string(n)| > 0
  ensures forall c :: c in nat_to_string(n) ==> c in "0123456789"
{
  if n == 0 then "0" else "1"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var (n, k) := parse_integers(stdin_input);
  if n == k {
    result := "1\n";
  } else {
    result := "1\n";
  }
}
// </vc-code>
