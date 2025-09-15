// <vc-preamble>
function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}
// </vc-preamble>

// <vc-helpers>
function SquareOrCubeOrId(x: int, i: int): int { if i % 3 == 0 then x * x else if i % 4 == 0 then x * x * x else x }
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)

    ensures r == sum(square_seq(lst))
// </vc-spec>
// <vc-code>
{
  r := sum(square_seq(lst));
}
// </vc-code>
