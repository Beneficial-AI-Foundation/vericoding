predicate ValidInput(a: int, b: int)
{
  a > 1 && b >= 0
}

function SocketsAfterStrips(strips: int, a: int): int
  requires a > 1 && strips >= 0
{
  1 + strips * (a - 1)
}

function CeilingDivision(x: int, y: int): int
  requires y > 0
{
  if x % y == 0 then x / y
  else if x >= 0 then x / y + 1
  else x / y
}

function MinStripsNeeded(a: int, b: int): int
  requires ValidInput(a, b)
{
  if b <= 1 then 0
  else CeilingDivision(b - 1, a - 1)
}

predicate CorrectResult(a: int, b: int, result: int)
  requires ValidInput(a, b)
{
  result >= 0 &&
  SocketsAfterStrips(result, a) >= b &&
  (result == 0 || SocketsAfterStrips(result - 1, a) < b)
}

// <vc-helpers>
lemma lemma_MinStripsNeeded_properties(a: int, b: int)
  requires ValidInput(a, b)
  ensures SocketsAfterStrips(MinStripsNeeded(a, b), a) >= b
  ensures MinStripsNeeded(a, b) == 0 || SocketsAfterStrips(MinStripsNeeded(a, b) - 1, a) < b
{
  var k := MinStripsNeeded(a, b);
  if b <= 1 {
    // k == 0
    assert SocketsAfterStrips(0, a) == 1; // 1 + 0 * (a - 1) == 1
    assert SocketsAfterStrips(0, a) >= b; // 1 >= b (since b <= 1)
    // k == 0, so no second condition to check
  } else {
    // b > 1, so k = CeilingDivision(b - 1, a - 1)
    var N := b - 1;
    var D := a - 1;
    // N > 0, D > 0 (since b > 1, a > 1)

    // Prove SocketsAfterStrips(k, a) >= b
    // k = CeilingDivision(N, D)
    // D * k >= N
    // (a - 1) * CeilingDivision(b - 1, a - 1) >= b - 1
    // (a - 1) * k >= b - 1
    // 1 + (a - 1) * k >= b
    // SocketsAfterStrips(k, a) >= b
    calc {
      SocketsAfterStrips(k, a);
      1 + k * (a - 1);
    }
    if N % D == 0 {
      assert k == N / D;
      assert k * D == N;
      assert 1 + N >= b; // N = b - 1
    } else {
      assert k == N / D + 1;
      assert k * D > N;
      assert (k - 1) * D < N; // k-1 = N / D
      assert 1 + k * D > 1 + N;
      assert 1 + k * D >= b;
    }


    // Prove SocketsAfterStrips(k - 1, a) < b if k > 0
    if k > 0 {
      // k > 0 implies CeilingDivision(b-1, a-1) > 0, which means b-1 > 0, so b > 1.
      // This is consistent with the 'else' branch condition.
      // We know (k - 1) * D < N
      // (k - 1) * (a - 1) < b - 1
      // 1 + (k - 1) * (a - 1) < b
      // SocketsAfterStrips(k - 1, a) < b
      calc {
        SocketsAfterStrips(k - 1, a);
        1 + (k - 1) * (a - 1);
      }
      if N % D == 0 {
        assert k - 1 == (N / D) - 1;
        assert (k - 1) * D == N - D;
        assert 1 + (N - D) < 1 + N;
        assert 1 + (N - D) < b; // since N = b - 1, N - D = b - 1 - D. This is < b
      } else {
        assert k - 1 == N / D;
        assert (k - 1) * D <= N;
        assert (k - 1) * D == N - (N % D);
        assert (k - 1) * D < N;
        assert 1 + (k - 1) * D < 1 + N;
        assert 1 + (k - 1) * D < b; // since N = b - 1
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, result)
// </vc-spec>
// <vc-code>
{
  assert ValidInput(a, b);
  result := MinStripsNeeded(a, b);
  lemma_MinStripsNeeded_properties(a, b);
  assert SocketsAfterStrips(result, a) >= b;
  assert result == 0 || SocketsAfterStrips(result - 1, a) < b;
}
// </vc-code>

