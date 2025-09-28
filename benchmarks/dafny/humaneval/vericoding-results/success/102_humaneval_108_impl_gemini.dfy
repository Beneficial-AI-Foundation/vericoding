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
/* helper modified by LLM (iteration 3): added body to prove lemma about set cardinality */
lemma CountSetLemma(arr: seq<int>, i: int)
    requires 0 <= i < |arr|
    ensures |(set j | 0 <= j < i+1 && digitSumFunc(arr[j]) > 0)| ==
            |(set j | 0 <= j < i   && digitSumFunc(arr[j]) > 0)| + (if digitSumFunc(arr[i]) > 0 then 1 else 0)
{
    var s_full := set j | 0 <= j < i+1 && digitSumFunc(arr[j]) > 0;
    var s_prefix := set j | 0 <= j < i && digitSumFunc(arr[j]) > 0;
    if digitSumFunc(arr[i]) > 0 {
        var s_union := s_prefix + {i};
        assert s_full == s_union;
        assert i !in s_prefix;
    } else {
        assert s_full == s_prefix;
    }
}
// </vc-helpers>

// <vc-spec>
method count_nums(arr: seq<int>) returns (count: int)
    requires ValidInput(arr)
    ensures ValidOutput(arr, count)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added invariant and removed redundant if-check */
  count := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant count == |set j | 0 <= j < i && digitSumFunc(arr[j]) > 0|
    invariant 0 <= count <= i
  {
    CountSetLemma(arr, i);
    var ds := digitSum(arr[i]);
    if ds > 0 {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
