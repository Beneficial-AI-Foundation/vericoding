// <vc-helpers>
lemma SumOfFourPositiveEvensMinimum()
    ensures forall a, b, c, d :: a > 0 && a % 2 == 0 && b > 0 && b % 2 == 0 && 
            c > 0 && c % 2 == 0 && d > 0 && d % 2 == 0 ==> a + b + c + d >= 8

lemma CanConstructSumOfFourPositiveEvens(n: int)
    requires n >= 8 && n % 2 == 0
    ensures exists a, b, c, d :: a > 0 && a % 2 == 0 && b > 0 && b % 2 == 0 && 
            c > 0 && c % 2 == 0 && d > 0 && d % 2 == 0 && a + b + c + d == n
{
    var a, b, c := 2, 2, 2;
    var d := n - 6;
    assert d == n - a - b - c;
    assert d >= 2 && d % 2 == 0;
    assert a + b + c + d == n;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_equal_to_sum_even(n: int) returns (b : bool)
Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers.
*/
// </vc-description>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b: bool)
    ensures b <==> (n >= 8 && n % 2 == 0)
// </vc-spec>
// <vc-code>
{
    if n < 8 || n % 2 != 0 {
        b := false;
    } else {
        b := true;
        CanConstructSumOfFourPositiveEvens(n);
    }
}
// </vc-code>
