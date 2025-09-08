Given two integers A and B (each between 1 and 3 inclusive), determine if there exists 
an integer C (also between 1 and 3 inclusive) such that the product A × B × C is odd.

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

lemma ProductIsOddIffAllFactorsOdd(a: int, b: int, c: int)
  ensures IsOdd(a * b * c) <==> (IsOdd(a) && IsOdd(b) && IsOdd(c))
{
    if IsOdd(a) && IsOdd(b) && IsOdd(c) {
        // All factors odd implies product is odd
        assert (a * b * c) % 2 == ((a % 2) * (b % 2) * (c % 2)) % 2;
        assert (a * b * c) % 2 == (1 * 1 * 1) % 2;
        assert (a * b * c) % 2 == 1;
    } else {
        // At least one factor is even implies product is even
        if a % 2 == 0 {
            assert (a * b * c) % 2 == 0;
        } else if b % 2 == 0 {
            assert (a * b * c) % 2 == 0;
        } else {
            assert c % 2 == 0;
            assert (a * b * c) % 2 == 0;
        }
    }
}

lemma ExistsOddProductEquivalence(a: int, b: int)
  requires ValidInput(a, b)
  ensures ExistsOddProduct(a, b) <==> ShouldAnswerYes(a, b)
{
    if ShouldAnswerYes(a, b) {
        // If both a and b are odd, choose c = 1 (which is odd)
        assert IsOdd(a) && IsOdd(b);
        assert 1 <= 1 <= 3 && IsOdd(a * b * 1);
        ProductIsOddIffAllFactorsOdd(a, b, 1);
    } else {
        // If either a or b is even (equals 2), then for any c, a*b*c is even
        forall c | 1 <= c <= 3 
            ensures !IsOdd(a * b * c)
        {
            ProductIsOddIffAllFactorsOdd(a, b, c);
        }
    }
}

method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
{
    ExistsOddProductEquivalence(a, b);
    
    if a == 2 || b == 2 {
        result := "No";
    } else {
        result := "Yes";
    }
}
