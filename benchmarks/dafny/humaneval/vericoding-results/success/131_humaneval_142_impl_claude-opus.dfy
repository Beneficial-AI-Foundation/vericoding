// <vc-preamble>

function transform_element(value: int, index: int): int
{
    if index % 3 == 0 then value * value
    else if index % 4 == 0 then value * value * value
    else value
}

function sum_partial(lst: seq<int>, n: int): int
    requires 0 <= n <= |lst|
{
    if n == 0 then 0
    else sum_partial(lst, n-1) + transform_element(lst[n-1], n-1)
}

function sum_transformed(lst: seq<int>): int
{
    sum_partial(lst, |lst|)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (result: int)
    ensures result == sum_transformed(lst)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant result == sum_partial(lst, i)
  {
    result := result + transform_element(lst[i], i);
    i := i + 1;
  }
}
// </vc-code>
