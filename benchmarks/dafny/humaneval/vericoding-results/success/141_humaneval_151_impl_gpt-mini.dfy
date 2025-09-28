// <vc-preamble>

datatype Number = Int(i: int) | Real(r: real)

function IsInteger(r: real): bool
{
    r == r.Floor as real
}

predicate IsPositiveOddInteger(n: Number)
{
    match n
    case Int(i) => i > 0 && i % 2 == 1
    case Real(r) => IsInteger(r) && r > 0.0 && (r.Floor as int) % 2 == 1
}

function SquareValue(n: Number): int
    requires IsPositiveOddInteger(n)
    ensures SquareValue(n) > 0
{
    match n
    case Int(i) => i * i
    case Real(r) => (r.Floor as int) * (r.Floor as int)
}

function SumOfSquares(lst: seq<Number>, i: nat): int
    requires i <= |lst|
    ensures SumOfSquares(lst, i) >= 0
{
    if i == 0 then 0
    else if IsPositiveOddInteger(lst[i-1]) then
        SquareValue(lst[i-1]) + SumOfSquares(lst, i-1)
    else
        SumOfSquares(lst, i-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute square when number is positive odd integer */
function SquareIfPositiveOdd(n: Number): int
  ensures SquareIfPositiveOdd(n) >= 0
  ensures IsPositiveOddInteger(n) ==> SquareIfPositiveOdd(n) == SquareValue(n)
  ensures !IsPositiveOddInteger(n) ==> SquareIfPositiveOdd(n) == 0
{
  match n
  case Int(i) => if i > 0 && i % 2 == 1 then i * i else 0
  case Real(r) => if IsInteger(r) && r > 0.0 && (r.Floor as int) % 2 == 1 then (r.Floor as int) * (r.Floor as int) else 0
}

// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<Number>) returns (result: int)
    ensures result >= 0
    ensures result == SumOfSquares(lst, |lst|)
    ensures |lst| == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): iterate through list and accumulate sum of squares of positive odd integers */
  var k := 0;
  result := 0;
  while k < |lst|
    invariant 0 <= k <= |lst|
    invariant result >= 0
    invariant result == SumOfSquares(lst, k)
  {
    if IsPositiveOddInteger(lst[k]) {
      result := result + SquareValue(lst[k]);
    }
    k := k + 1;
  }
}

// </vc-code>
