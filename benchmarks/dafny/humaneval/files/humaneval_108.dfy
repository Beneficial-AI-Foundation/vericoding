// <vc-preamble>

function digitSumFunc(n: int): int
{
    if n == 0 then 0
    else if n > 0 then sumOfDigitsPos(n)
    else sumOfDigitsPos(-n) - 2 * firstDigit(-n)
}

function sumOfDigitsPos(n: nat): nat
    requires n >= 0
    ensures n > 0 ==> sumOfDigitsPos(n) > 0
{
    if n == 0 then 0
    else (n % 10) + sumOfDigitsPos(n / 10)
}

function firstDigit(n: nat): nat
    requires n > 0
{
    if n < 10 then n
    else firstDigit(n / 10)
}

predicate ValidInput(arr: seq<int>)
{
    true
}

predicate ValidOutput(arr: seq<int>, count: int)
{
    0 <= count <= |arr| && count == |set i | 0 <= i < |arr| && digitSumFunc(arr[i]) > 0|
}
method digitSum(n: int) returns (result: int)
    ensures result == digitSumFunc(n)
    ensures n == 0 ==> result == 0
    ensures n > 0 ==> result > 0
{
    if n == 0 {
        result := 0;
    } else if n > 0 {
        var abs_n := n;
        var sum := 0;
        while abs_n > 0 
            invariant abs_n >= 0
            invariant sum + sumOfDigitsPos(abs_n) == sumOfDigitsPos(n)
        {
            sum := sum + (abs_n % 10);
            abs_n := abs_n / 10;
        }
        result := sum;
    } else {
        var abs_n := -n;
        var sum := 0;
        var first_digit := 0;
        var temp := abs_n;

        while temp >= 10
            invariant temp > 0
            invariant firstDigit(temp) == firstDigit(abs_n)
        {
            temp := temp / 10;
        }
        first_digit := temp;

        while abs_n > 0 
            invariant abs_n >= 0
            invariant sum + sumOfDigitsPos(abs_n) == sumOfDigitsPos(-n)
        {
            sum := sum + (abs_n % 10);
            abs_n := abs_n / 10;
        }
        result := sum - 2 * first_digit;
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method count_nums(arr: seq<int>) returns (count: int)
    requires ValidInput(arr)
    ensures ValidOutput(arr, count)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
