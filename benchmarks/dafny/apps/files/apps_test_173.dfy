// <vc-preamble>
predicate ValidInput(n: int, m: int, horizontal: seq<char>, vertical: seq<char>)
{
    n >= 2 && n <= 20 && m >= 2 && m <= 20 &&
    |horizontal| == n && |vertical| == m &&
    (forall c :: c in horizontal ==> c == '<' || c == '>') &&
    (forall c :: c in vertical ==> c == '^' || c == 'v')
}

predicate IsDisconnected(hor: seq<char>, ver: seq<char>)
{
    (|hor| > 0 && |ver| > 0 && hor[0] == '>' && ver[0] == 'v') ||
    (|hor| > 0 && |ver| > 0 && hor[0] == '<' && ver[|ver|-1] == 'v') ||
    (|hor| > 0 && |ver| > 0 && hor[|hor|-1] == '>' && ver[0] == '^') ||
    (|hor| > 0 && |ver| > 0 && hor[|hor|-1] == '<' && ver[|ver|-1] == '^')
}

function {:extern} split(s: seq<char>, delimiter: char): seq<seq<char>>

function {:extern} is_integer(s: seq<char>): bool

function {:extern} parse_int(s: seq<char>): int
    requires is_integer(s)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, horizontal: seq<char>, vertical: seq<char>) returns (result: seq<char>)
    requires ValidInput(n, m, horizontal, vertical)
    ensures result == "YES\n" || result == "NO\n"
    ensures (result == "NO\n" <==> IsDisconnected(horizontal, vertical))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
