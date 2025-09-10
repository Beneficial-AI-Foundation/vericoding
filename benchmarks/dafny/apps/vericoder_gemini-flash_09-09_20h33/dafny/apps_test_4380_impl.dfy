predicate ValidInput(a: int, b: int)
{
    1 <= a <= 3 && 1 <= b <= 3
}

predicate IsOdd(n: int)
{
    n % 2 == 1
}

predicate ExistsOddProduct(a: int, b: int)
  requires ValidInput(a, b)
{
    exists c :: 1 <= c <= 3 && IsOdd(a * b * c)
}

function ShouldAnswerYes(a: int, b: int): bool
  requires ValidInput(a, b)
{
    a != 2 && b != 2
}

// <vc-helpers>
lemma lemma_ExistsOddProduct_implies_ShouldAnswerYes(a: int, b: int)
  requires ValidInput(a, b)
  ensures ExistsOddProduct(a, b) ==> ShouldAnswerYes(a, b)
{
  if (ExistsOddProduct(a, b)) {
    // If ExistsOddProduct is true, then there exists a c (1, 2, or 3)
    // such that a * b * c is odd.
    // For a product of integers to be odd, all its factors must be odd.
    // So, a must be odd, b must be odd, and c must be odd.
    // From ValidInput(a, b), a, b can be 1, 2, 3.
    // If a is odd, a is 1 or 3. So a != 2.
    // If b is odd, b is 1 or 3. So b != 2.
    // Therefore, a != 2 && b != 2, which means ShouldAnswerYes.
    // This is explicitly asserted below to make the proof go through.
    assert (a % 2 == 1 && b % 2 == 1); // a and b must be odd for a*b*c to be odd
  }
}

lemma lemma_ShouldAnswerYes_iff_ExistsOddProduct(a: int, b: int)
  requires ValidInput(a, b)
  ensures ShouldAnswerYes(a, b) <==> ExistsOddProduct(a, b)
{
  // Prove ShouldAnswerYes(a, b) ==> ExistsOddProduct(a, b)
  if (a != 2 && b != 2) {
    // If neither a nor b is 2, then a and b are odd (1 or 3).
    // Their product a * b will also be odd.
    // We can pick c = 1, which is odd.
    // Then a * b * c is odd * odd * odd = odd.
    // Thus ExistsOddProduct holds.
    assert ExistsOddProduct(a, b) by {
      // If a is 1 or 3, and b is 1 or 3, then a*b is odd.
      assert a % 2 == 1; // since a != 2 and 1 <= a <= 3, a must be 1 or 3
      assert b % 2 == 1; // since b != 2 and 1 <= b <= 3, b must be 1 or 3
      assert (a * b) % 2 == 1; // odd * odd is odd
      // Therefore, a*b*1 is odd, and 1 <= 1 <= 3.
      assert IsOdd(a * b * 1);
      assert 1 <= 1 <= 3;
    }
  }
  // Prove ExistsOddProduct(a, b) ==> ShouldAnswerYes(a, b)
  lemma_ExistsOddProduct_implies_ShouldAnswerYes(a, b);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
// </vc-spec>
// <vc-code>
{
  lemma_ShouldAnswerYes_iff_ExistsOddProduct(a, b); // The ensures clause links ShouldAnswerYes and ExistsOddProduct
  if ShouldAnswerYes(a, b) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

