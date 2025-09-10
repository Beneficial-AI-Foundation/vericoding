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
function Desired(i: int): int
  requires i >= 0
{
  if i < 9 then i + 1
  else if i == 9 then 19
  else 19 + (i - 9)
}

lemma Desired_positive(i: int)
  requires i >= 0
  ensures Desired(i) > 0
{
  if i < 9 {
    assert Desired(i) == i + 1;
    assert i + 1 > 0;
  } else if i == 9 {
    assert Desired(i) == 19;
    assert 19 > 0;
  } else {
    assert Desired(i) == 19 + (i - 9);
    assert 19 + (i - 9) > 0;
  }
}

lemma Desired_monotone(i: int, j: int)
  requires 0 <= i < j
  ensures Desired(i) < Desired(j)
{
  if j < 9 {
    // both i and j are < 9
    assert i < 9;
    assert Desired(i) == i + 1;
    assert Desired(j) == j + 1;
    assert i + 1 < j + 1;
  } else if j == 9 {
    // j == 9, so i <= 8
    assert i < 9;
    assert Desired(i) == i + 1;
    assert Desired(j) == 19;
    assert i + 1 <= 9;
    assert 9 < 19;
    assert i + 1 < 19;
  } else {
    // j > 9
    if i < 9 {
      // i < 9, j > 9
      assert Desired(i) == i + 1;
      assert Desired(j) == 19 + (j - 9);
      assert i + 1 <= 9;
      assert 9 < 19 + (j - 9);
      assert i + 1 < Desired(j);
    } else if i == 9 {
      // i == 9, j > 9
      assert Desired(i) == 19;
      assert Desired(j) == 19 + (j - 9);
      assert 19 < 19 + (j - 9);
    } else {
      // both i and j > 9
      assert Desired(i) == 19 + (i - 9);
      assert Desired(j) == 19 + (j - 9);
      assert i - 9 < j - 9;
      assert 19 + (i - 9) < 19 + (j - 9);
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
  var a := new int[k];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> a[j] == Desired(j)
  {
    a[i] := Desired(i);
    i := i + 1;
  }
  assert i == k;
  result := a[..];

  // Elements equal Desired
  assert forall j :: 0 <= j < k ==> result[j] == Desired(j)
  {
    fix j;
    assume 0 <= j < k;
    assert result[j] == a[j];
    assert a[j] == Desired(j);
  }

  // Positivity
  assert forall j :: 0 <= j < k ==> result[j] > 0
  {
    fix j;
    assume 0 <= j < k;
    assert result[j] == Desired(j);
    call Desired_positive(j);
    assert result[j] > 0;
  }

  // Strictly increasing
  assert forall i0 :: 0 <= i0 < k - 1 ==> result[i0] < result[i0 + 1]
  {
    fix i0;
    assume 0 <= i0 < k - 1;
    assert result[i0] == Desired(i0);
    assert result[i0 + 1] == Desired(i0 + 1);
    call Desired_monotone(i0, i0 + 1);
    assert result[i0] < result[i0 + 1];
  }

  // Fixed initial values
  if k >= 1 {
    assert result[0] == Desired(0);
    assert result[0] == 1;
  }
  if k >= 2 {
    assert result[1] == Desired(1);
    assert result[1] == 2;
  }
  if k >= 3 {
    assert result[2] == Desired(2);
    assert result[2] == 3;
  }
  if k >= 4 {
    assert result[3] == Desired(3);
    assert result[3] == 4;
  }
  if k >= 5 {
    assert result[4] == Desired(4);
    assert result[4] == 5;
  }
  if k >= 6 {
    assert result[5] == Desired(5);
    assert result[5] == 6;
  }
  if k >= 7 {
    assert result[6] == Desired(6);
    assert result[6] == 7;
  }
  if k >= 8 {
    assert result[7] == Desired(7);
    assert result[7] == 8;
  }
  if k >= 9 {
    assert result[8] == Desired(8);
    assert result[8] == 9;
  }
  if k >= 10 {
    assert result[9] == Desired(9);
    assert result[9] == 19;
  }
}
// </vc-code>

