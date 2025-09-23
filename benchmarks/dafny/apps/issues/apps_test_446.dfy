// <vc-preamble>
function power(base: int, exp: int): int
  requires base >= 0 && exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

predicate ValidInput(n: int) {
  n >= 1 && n <= 100000
}

predicate IsBeautifulNumber(x: int) {
  exists k :: 1 <= k <= 9 && x == (power(2, k) - 1) * power(2, k - 1)
}

predicate IsLargestBeautifulDivisor(n: int, result: int) {
  result >= 1 &&
  n % result == 0 &&
  IsBeautifulNumber(result) &&
  forall k :: 1 <= k <= 9 && n % ((power(2, k) - 1) * power(2, k - 1)) == 0 ==> 
    result >= (power(2, k) - 1) * power(2, k - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires ValidInput(n)
  ensures IsLargestBeautifulDivisor(n, result)
// </vc-spec>
// <vc-code>
{
    var ans := 1;
    assert power(2, 1) == 2;
    assert power(2, 0) == 1;
    assert (power(2, 1) - 1) * power(2, 0) == 1;
    assert n % 1 == 0;

    var k := 1;
    while k < 10
        invariant 1 <= k <= 10
        invariant ans >= 1
        invariant n % ans == 0
        invariant exists j :: 1 <= j <= 9 && ans == (power(2, j) - 1) * power(2, j - 1)
        invariant forall j :: 1 <= j < k && n % ((power(2, j) - 1) * power(2, j - 1)) == 0 ==> ans >= (power(2, j) - 1) * power(2, j - 1)
    {
        var twoToK := 1;
        var i := 0;
        while i < k
            invariant 0 <= i <= k
            invariant twoToK == power(2, i)
        {
            twoToK := twoToK * 2;
            i := i + 1;
        }
        assert twoToK == power(2, k);

        var twoToKMinus1 := 1;
        if k > 1 {
            var j := 0;
            while j < k - 1
                invariant 0 <= j <= k - 1
                invariant twoToKMinus1 == power(2, j)
            {
                twoToKMinus1 := twoToKMinus1 * 2;
                j := j + 1;
            }
        }
        assert twoToKMinus1 == power(2, k - 1);

        var v := (twoToK - 1) * twoToKMinus1;
        assert v == (power(2, k) - 1) * power(2, k - 1);

        if n % v == 0 {
            ans := v;
        }
        k := k + 1;
    }
    result := ans;
}
// </vc-code>
