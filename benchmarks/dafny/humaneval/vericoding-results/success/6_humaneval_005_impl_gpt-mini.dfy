// <vc-preamble>

predicate ValidInput(numbers: seq<int>, delimiter: int)
{
    true // Any sequence and delimiter are valid inputs
}

predicate ValidOutput(numbers: seq<int>, delimiter: int, result: seq<int>)
{
    if |numbers| <= 1 then
        result == numbers
    else
        |result| == 2 * |numbers| - 1 &&
        (forall i :: 0 <= i < |numbers| ==> result[2 * i] == numbers[i]) &&
        (forall i :: 0 <= i < |numbers| - 1 ==> result[2 * i + 1] == delimiter)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemmas for division properties */
lemma DivMulHalf(n: int)
  ensures (2*n)/2 == n
  ensures (2*n)%2 == 0
{
  assert (2*n)/2 == n;
  assert (2*n)%2 == 0;
}

/* helper modified by LLM (iteration 5): lemmas for division properties */
lemma DivOdd(n: int)
  ensures (2*n+1)/2 == n
  ensures (2*n+1)%2 == 1
{
  assert (2*n+1)/2 == n;
  assert (2*n+1)%2 == 1;
}

/* helper modified by LLM (iteration 5): index bound facts for array positions */
lemma IndexBounds1(n: int, i: int)
  requires n >= 1
  requires 0 <= i < n
  ensures 2*i < 2*n - 1
{
  // 2*i <= 2*n - 2 < 2*n - 1
  assert 2*i <= 2*n - 2;
  assert 2*n - 2 < 2*n - 1;
  assert 2*i < 2*n - 1;
}

/* helper modified by LLM (iteration 5): index bound facts for odd positions */
lemma IndexBounds2(n: int, i: int)
  requires n >= 2
  requires 0 <= i < n-1
  ensures 2*i + 1 < 2*n - 1
{
  // 2*i+1 <= 2*(n-2)+1 = 2*n-3 < 2*n-1
  assert 2*i + 1 <= 2*(n-2) + 1;
  assert 2*(n-2) + 1 == 2*n - 3;
  assert 2*n - 3 < 2*n - 1;
  assert 2*i + 1 < 2*n - 1;
}

// </vc-helpers>

// <vc-spec>
method InsertDelimiter(numbers: seq<int>, delimiter: int) returns (result: seq<int>)
    requires ValidInput(numbers, delimiter)
    ensures ValidOutput(numbers, delimiter, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): build result with array and strengthened invariants */
{
  if |numbers| <= 1 {
    result := numbers;
    return;
  }
  var n := |numbers|;
  var L := 2 * n - 1;
  var a := new int[L];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[2*j] == numbers[j]
    invariant forall j :: 0 <= j < i-1 ==> a[2*j+1] == delimiter
    invariant i > 0 && i-1 < n-1 ==> a[2*(i-1)+1] == delimiter
  {
    assert 2*i < L;
    a[2*i] := numbers[i];
    if i < n-1 {
      assert 2*i+1 < L;
      a[2*i+1] := delimiter;
    }
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
