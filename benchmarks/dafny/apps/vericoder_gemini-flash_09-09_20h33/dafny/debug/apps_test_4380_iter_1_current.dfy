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
  // This lemma is not directly used by the solver method
  // but it proves a relationship between the predicates.
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
  }
  // Prove ExistsOddProduct(a, b) ==> ShouldAnswerYes(a, b)
  if (ExistsOddProduct(a, b)) {
    // If ExistsOddProduct is true, then there exists a c (1, 2, or 3)
    // such that a * b * c is odd.
    // For a product of integers to be odd, all its factors must be odd.
    // So, a must be odd, b must be odd, and c must be odd.
    // From ValidInput(a, b), a, b can be 1, 2, 3.
    // If a is odd, a is 1 or 3. So a != 2.
    // If b is odd, b is 1 or 3. So b != 2.
    // Therefore, a != 2 && b != 2, which means ShouldAnswerYes.
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
// </vc-spec>
// <vc-code>
{
  if ShouldAnswerYes(a, b) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

