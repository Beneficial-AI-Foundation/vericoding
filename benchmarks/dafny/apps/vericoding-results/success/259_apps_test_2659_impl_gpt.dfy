function SumOfDigits(n: int): int
  requires n >= 0
{
  if n < 10 then n
  else (n % 10) + SumOfDigits(n / 10)
}

predicate ValidOutput(result: seq<int>, k: int)
{
  |result| == k &&
  (forall i :: 0 <= i < k ==> result[i] > 0) &&
  (forall i :: 0 <= i < k - 1 ==> result[i] < result[i + 1]) &&
  (k >= 1 ==> result[0] == 1) &&
  (k >= 2 ==> result[1] == 2) &&
  (k >= 3 ==> result[2] == 3) &&
  (k >= 4 ==> result[3] == 4) &&
  (k >= 5 ==> result[4] == 5) &&
  (k >= 6 ==> result[5] == 6) &&
  (k >= 7 ==> result[6] == 7) &&
  (k >= 8 ==> result[7] == 8) &&
  (k >= 9 ==> result[8] == 9) &&
  (k >= 10 ==> result[9] == 19)
}

// <vc-helpers>
function Val(i: int): int
  requires i >= 0
{
  if i < 9 then i + 1 else if i == 9 then 19 else i + 10
}

lemma ValPositive(i: int)
  requires i >= 0
  ensures Val(i) > 0
{
  if i < 9 {
    assert Val(i) == i + 1;
    assert i + 1 > 0;
  } else if i == 9 {
    assert Val(i) == 19;
    assert 19 > 0;
  } else {
    assert i >= 10;
    assert Val(i) == i + 10;
    assert i + 10 > 0;
  }
}

lemma ValIncreasing(i: int)
  requires i > 0
  ensures Val(i - 1) < Val(i)
{
  if i < 9 {
    assert Val(i - 1) == (i - 1) + 1;
    assert Val(i) == i + 1;
    assert (i - 1) + 1 < i + 1;
  } else if i == 9 {
    assert Val(i - 1) == 9;
    assert Val(i) == 19;
    assert 9 < 19;
  } else {
    if i == 10 {
      assert Val(i - 1) == 19;
      assert Val(i) == 20;
      assert 19 < 20;
    } else {
      assert i >= 11;
      assert Val(i - 1) == (i - 1) + 10;
      assert Val(i) == i + 10;
      assert (i - 1) + 10 < i + 10;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
// </vc-spec>
// <vc-code>
{
  var r: seq<int> := [];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == Val(j)
    invariant forall j :: 0 <= j < i ==> r[j] > 0
    invariant forall j :: 0 <= j < i - 1 ==> r[j] < r[j + 1]
  {
    // Prepare facts for the new element
    ValPositive(i);
    if i > 0 {
      ValIncreasing(i);
    }
    r := r + [Val(i)];
    i := i + 1;
  }
  result := r;
}
// </vc-code>

