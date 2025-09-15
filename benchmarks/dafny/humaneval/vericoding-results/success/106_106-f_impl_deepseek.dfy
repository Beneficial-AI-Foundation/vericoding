// <vc-preamble>
function factorial_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * factorial_spec(n - 1)
}
function sum_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n + sum_spec(n - 1)
}
// </vc-preamble>

// <vc-helpers>
function ComputeEvenIndex(i: int): int
  requires i >= 0
  ensures ComputeEvenIndex(i) == factorial_spec(i)
{
  if i == 0 then 1 else i * ComputeEvenIndex(i-1)
}
function ComputeOddIndex(i: int): int
  requires i >= 0
  ensures ComputeOddIndex(i) == sum_spec(i)
{
  if i == 0 then 1 else i + ComputeOddIndex(i-1)
}
lemma EvenIndexLemma(i: int, result: seq<int>)
  requires i >= 0 && |result| > i && i % 2 == 0
  requires result[i] == ComputeEvenIndex(i)
  ensures result[i] == factorial_spec(i)
{}
lemma OddIndexLemma(i: int, result: seq<int>)
  requires i >= 0 && |result| > i && i % 2 != 0
  requires result[i] == ComputeOddIndex(i)
  ensures result[i] == sum_spec(i)
{}
// </vc-helpers>

// <vc-spec>
method f(n : int) returns (result : seq<int>)

  requires n >= 1

  ensures |result| == n
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added loop invariant strengthening for postcondition proof */
{
  result := [];
  var i := 0;
  while i < n
    invariant |result| == i
    invariant i >= 0 && i <= n
    invariant forall j: int :: 0 <= j < i && j % 2 == 0 ==> result[j] == ComputeEvenIndex(j)
    invariant forall j: int :: 0 <= j < i && j % 2 != 0 ==> result[j] == ComputeOddIndex(j)
    invariant forall j: int :: 0 <= j < i && j % 2 == 0 ==> result[j] == factorial_spec(j)
    invariant forall j: int :: 0 <= j < i && j % 2 != 0 ==> result[j] == sum_spec(j)
  {
    if i % 2 == 0 {
      result := result + [ComputeEvenIndex(i)];
      EvenIndexLemma(i, result);
    } else {
      result := result + [ComputeOddIndex(i)];
      OddIndexLemma(i, result);
    }
    i := i + 1;
  }
}
// </vc-code>
