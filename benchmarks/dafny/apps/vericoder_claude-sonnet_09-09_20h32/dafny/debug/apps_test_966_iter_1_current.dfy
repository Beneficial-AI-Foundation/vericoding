predicate ValidInput(y: int)
{
    1000 <= y <= 9000
}

function HasDistinctDigits(n: int): bool
{
    var digits := NumberToDigits(n);
    AllDistinct(digits)
}

function NumberToDigits(n: int): seq<int>
{
    if n == 0 then [0]
    else if n > 0 then NumberToDigitsHelper(n, [])
    else NumberToDigitsHelper(-n, [])
}

function NumberToDigitsHelper(n: int, acc: seq<int>): seq<int>
requires n >= 0
decreases n
{
    if n == 0 then acc
    else NumberToDigitsHelper(n / 10, [n % 10] + acc)
}

predicate AllDistinct(digits: seq<int>)
{
    forall i, j :: 0 <= i < j < |digits| ==> digits[i] != digits[j]
}

// <vc-helpers>
lemma NumberToDigitsCorrect(n: int)
requires n >= 0
ensures var digits := NumberToDigits(n); digits != [] && forall d :: d in digits ==> 0 <= d <= 9
{
    if n == 0 {
        assert NumberToDigits(0) == [0];
    } else {
        NumberToDigitsHelperCorrect(n, []);
    }
}

lemma NumberToDigitsHelperCorrect(n: int, acc: seq<int>)
requires n >= 0
requires forall d :: d in acc ==> 0 <= d <= 9
ensures var result := NumberToDigitsHelper(n, acc); forall d :: d in result ==> 0 <= d <= 9
decreases n
{
    if n == 0 {
        assert NumberToDigitsHelper(n, acc) == acc;
    } else {
        assert 0 <= n % 10 <= 9;
        NumberToDigitsHelperCorrect(n / 10, [n % 10] + acc);
    }
}

lemma HasDistinctDigitsDecidable(n: int)
ensures HasDistinctDigits(n) || !HasDistinctDigits(n)
{
}

lemma FiniteSearch(y: int, bound: int)
requires ValidInput(y)
requires bound > y
ensures exists result :: y < result <= bound && HasDistinctDigits(result)
{
    if bound <= y + 1 {
        assert false;
    } else if HasDistinctDigits(bound) {
        assert y < bound <= bound && HasDistinctDigits(bound);
    } else {
        FiniteSearch(y, bound - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(y: int) returns (result: int)
requires ValidInput(y)
ensures result > y
ensures HasDistinctDigits(result)
ensures forall n :: y < n < result ==> !HasDistinctDigits(n)
// </vc-spec>
// <vc-code>
{
    result := y + 1;
    
    while !HasDistinctDigits(result)
    invariant result > y
    invariant forall n :: y < n < result ==> !HasDistinctDigits(n)
    decreases 9876 - result
    {
        assert result < 9876 by {
            if result >= 9876 {
                assert HasDistinctDigits(1023);
                FiniteSearch(y, 1023);
                assert false;
            }
        }
        result := result + 1;
    }
}
// </vc-code>

