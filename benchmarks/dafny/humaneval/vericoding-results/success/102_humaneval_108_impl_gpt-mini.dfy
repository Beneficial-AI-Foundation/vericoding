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
/* helper modified by LLM (iteration 5): lemma to relate count when extending range by one */
lemma Count_step(arr: seq<int>, i: int)
  requires 0 <= i < |arr|
  ensures |set j | 0 <= j < i+1 && digitSumFunc(arr[j]) > 0| == |set j | 0 <= j < i && digitSumFunc(arr[j]) > 0| + (if digitSumFunc(arr[i]) > 0 then 1 else 0)
{
  var oldset := set j | 0 <= j < i && digitSumFunc(arr[j]) > 0;
  var newset := set j | 0 <= j < i+1 && digitSumFunc(arr[j]) > 0;
  if digitSumFunc(arr[i]) > 0 {
    assert forall k :: k in newset ==> (k in oldset) || k == i;
    assert forall k :: (k in oldset) || k == i ==> k in newset;
    assert newset == oldset + {i};
    assert i !in oldset;
    assert |newset| == |oldset| + 1;
  } else {
    assert forall k :: k in newset ==> k in oldset;
    assert forall k :: k in oldset ==> k in newset;
    assert newset == oldset;
    assert |newset| == |oldset|;
  }
}

/* helper modified by LLM (iteration 5): cardinality upper bound lemma */
lemma Count_le_i(arr: seq<int>, i: int)
  requires 0 <= i <= |arr|
  ensures |set j | 0 <= j < i && digitSumFunc(arr[j]) > 0| <= i
{
  if i == 0 {
    assert |set j | 0 <= j < 0 && digitSumFunc(arr[j]) > 0| == 0;
  } else {
    Count_le_i(arr, i-1);
    // i-1 is in range [0, |arr|-1]
    if 0 <= i-1 && i-1 < |arr| {
      Count_step(arr, i-1);
      var prev := |set j | 0 <= j < i-1 && digitSumFunc(arr[j]) > 0|;
      var now := |set j | 0 <= j < i && digitSumFunc(arr[j]) > 0|;
      if digitSumFunc(arr[i-1]) > 0 {
        assert now == prev + 1;
        assert prev <= i-1;
        assert now <= i;
      } else {
        assert now == prev;
        assert now <= i-1;
        assert now <= i;
      }
    }
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
  /* code modified by LLM (iteration 5): maintain exact count invariant using Count_step and Count_le_i */
  count := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant 0 <= count <= |arr|
    invariant count == |set j | 0 <= j < i && digitSumFunc(arr[j]) > 0|
  {
    var prev := count;
    if digitSumFunc(arr[i]) > 0 {
      count := prev + 1;
    } else {
      count := prev;
    }
    Count_step(arr, i);
    assert count == |set j | 0 <= j < i+1 && digitSumFunc(arr[j]) > 0|;
    // use cardinality bound to maintain 0 <= count <= |arr|
    Count_le_i(arr, i+1);
    assert count <= i+1;
    assert i+1 <= |arr|;
    i := i + 1;
  }
}
// </vc-code>
