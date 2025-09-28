predicate ValidInput(n: int, m: int)
{
    2 <= n <= 100 && 2 <= m <= 100
}

function CountBlocks(n: int, m: int): int
    requires ValidInput(n, m)
{
    (n - 1) * (m - 1)
}

predicate CorrectOutput(n: int, m: int, blocks: int)
{
    ValidInput(n, m) && blocks == CountBlocks(n, m)
}

// <vc-helpers>
lemma CountBlocks_ge_1(n: int, m: int)
  requires ValidInput(n, m)
  ensures CountBlocks(n, m) >= 1
{
  assert CountBlocks(n, m) == (n - 1) * (m - 1);
  assert n - 1 >= 1;
  assert m - 1 >= 1;
  assert (n - 1) * (m - 1) >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (blocks: int)
    requires ValidInput(n, m)
    ensures CorrectOutput(n, m, blocks)
    ensures blocks >= 1
// </vc-spec>
// <vc-code>
{
  blocks := CountBlocks(n, m);
  CountBlocks_ge_1(n, m);
  assert blocks >= 1;
}
// </vc-code>

