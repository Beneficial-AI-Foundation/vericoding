function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

predicate ValidInput(n: int) {
    n > 0
}

// <vc-helpers>
lemma ParityDiv2(n: int)
  ensures n % 2 == 0 ==> (n - 1) / 2 + 1 == n / 2
  ensures n % 2 != 0 ==> (n - 1) / 2 == n / 2
{
  if n % 2 == 0 {
    assert (n - 1) / 2 + 1 == n / 2;
  } else {
    assert (n - 1) / 2 == n / 2;
  }
}

lemma AlternatingSumClosed(n: int)
    requires n > 0
    ensures AlternatingSum(n) == (if n % 2 == 0 then n / 2 else n / 2 - n)
    decreases n
{
  reveal AlternatingSum();
  if n == 1 {
    assert AlternatingSum(1) == -1;
    assert 1 % 2 != 0;
    assert 1 / 2 - 1 == -1;
  } else {
    AlternatingSumClosed(n - 1);
    if n % 2 == 0 {
      assert AlternatingSum(n) == AlternatingSum(n - 1) + n;
      assert (n - 1) % 2 != 0;
      assert AlternatingSum(n - 1) == (n - 1) / 2 - (n - 1);
      assert AlternatingSum(n) == (n - 1) / 2 - (n - 1) + n;
      ParityDiv2(n);
      assert (n - 1) / 2 + 1 == n / 2;
      assert AlternatingSum(n) == n / 2;
    } else {
      assert AlternatingSum(n) == AlternatingSum(n - 1) - n;
      assert (n - 1) % 2 == 0;
      assert AlternatingSum(n - 1) == (n - 1) / 2;
      ParityDiv2(n);
      assert (n - 1) / 2 == n / 2;
      assert AlternatingSum(n) == n / 2 - n;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == AlternatingSum(n)
    ensures n % 2 == 0 ==> result == n / 2
    ensures n % 2 != 0 ==> result == n / 2 - n
// </vc-spec>
// <vc-code>
{
  AlternatingSumClosed(n);
  if n % 2 == 0 {
    result := n / 2;
  } else {
    result := n / 2 - n;
  }
}
// </vc-code>

