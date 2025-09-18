// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max2(a: int, b: int): int
  ensures Max2(a,b) >= a && Max2(a,b) >= b
  ensures Max2(a,b) == a || Max2(a,b) == b
{
  if a >= b then a else b
}

function Max3(a: int, b: int, c: int): int
  ensures Max3(a,b,c) >= a && Max3(a,b,c) >= b && Max3(a,b,c) >= c
  ensures Max3(a,b,c) == a || Max3(a,b,c) == b || Max3(a,b,c) == c
{
  if Max2(a,b) >= c then Max2(a,b) else c
}
// </vc-helpers>

// <vc-spec>
method MaxOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result >= a && result >= b && result >= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  result := Max3(a, b, c);
}
// </vc-code>
