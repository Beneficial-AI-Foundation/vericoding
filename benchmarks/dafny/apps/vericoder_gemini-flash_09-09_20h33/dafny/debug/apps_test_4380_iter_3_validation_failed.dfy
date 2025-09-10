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
    // This justification is currently manual and needs to be formalized if Dafny
    // does not automatically deduce it.
    // Let's prove it by contradiction.
    // Assume ExistsOddProduct(a, b) is true, but ShouldAnswerYes(a, b) is false.
    // This means a = 2 or b = 2.
    // Case 1: a = 2.
    // If a = 2, then a * b * c = 2 * b * c. This product is always even,
    // regardless of b and c. This contradicts ExistsOddProduct(a, b) being true.
    // Case 2: b = 2.
    // If b = 2, then a * b * c = a * 2 * c. This product is always even,
    // regardless of a and c. This contradicts ExistsOddProduct(a, b) being true.
    // Since both cases lead to a contradiction, our assumption must be false.
    // Therefore, if ExistsOddProduct(a, b) is true, then ShouldAnswerYes(a, b)
    // must be true.
  }
}

lemma lemma_ShouldAnswerYes_iff_ExistsOddProduct(a: int, b: int)
  requires ValidInput(a, b)
  ensures ShouldAnswerYes(a, b) <==> ExistsOddProduct(a, b)
{
  // Prove ShouldAnswerYes(a, b) ==> ExistsOddProduct(a, b)
  if (ShouldAnswerYes(a, b)) {
    // If neither a nor b is 2, then a and b are odd (1 or 3).
    // Their product a * b will also be odd.
    // We can pick c = 1, which is odd.
    // Then a * b * c is odd * odd * odd = odd.
    // Thus ExistsOddProduct holds.
    assert (a == 1 || a == 3);
    assert (b == 1 || b == 3);
    assert IsOdd(a * b);
    assert ExistsOddProduct(a, b) by {
      // If a is 1 or 3, and b is 1 or 3, then a*b is odd.
      // Therefore, a*b*1 is odd, and 1 <= 1 <= 3.
      // So ExistsOddProduct(a, b) holds.
      // We need to show that for c=1, 1 <= c <= 3 and IsOdd(a*b*c).
      // Since a and b are not 2, and ValidInput(a,b) holds,
      // a can be 1 or 3, and b can be 1 or 3.
      // In all these cases (1*1, 1*3, 3*1, 3*3), a*b is odd.
      // So a*b*1 is odd.
      // Thus, 'exists c :: 1 <= c <= 3 && IsOdd(a * b * c)' holds for c=1.
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
  lemma_ShouldAnswerYes_iff_ExistsOddProduct(a, b); // To link ShouldAnswerYes and ExistsOddProduct
  if ShouldAnswerYes(a, b) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

