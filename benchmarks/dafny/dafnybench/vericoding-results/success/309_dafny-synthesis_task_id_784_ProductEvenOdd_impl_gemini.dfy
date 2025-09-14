// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

predicate IsFirstEven(evenIndex: int, lst: seq<int>)
    requires 0 <= evenIndex < |lst|
    requires IsEven(lst[evenIndex])
{
    forall i :: 0 <= i < evenIndex ==> IsOdd(lst[i])
}

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
    requires 0 <= oddIndex < |lst|
    requires IsOdd(lst[oddIndex])
{
    forall i :: 0 <= i < oddIndex ==> IsEven(lst[i])
}

method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: int, oddIndex : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|

    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed function signatures to name the return values. */
function findFirstEvenIndex(lst: seq<int>): (result: int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures 0 <= result < |lst|
  ensures IsEven(lst[result])
  ensures forall i :: 0 <= i < result ==> IsOdd(lst[i])
{
  if IsEven(lst[0]) then 0
  else 1 + findFirstEvenIndex(lst[1..])
}

function findFirstOddIndex(lst: seq<int>): (result: int)
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= result < |lst|
  ensures IsOdd(lst[result])
  ensures forall i :: 0 <= i < result ==> IsEven(lst[i])
{
  if IsOdd(lst[0]) then 0
  else 1 + findFirstOddIndex(lst[1..])
}
// </vc-helpers>

// <vc-spec>
method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Use helper functions to find indices and compute product. */
  var evenIndex := findFirstEvenIndex(lst);
  var oddIndex := findFirstOddIndex(lst);
  product := lst[evenIndex] * lst[oddIndex];
}
// </vc-code>
